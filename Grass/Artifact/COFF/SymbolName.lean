import Grass.Artifact.COFF.Symbol

/-!
# Typed COFF symbol names

The eight-byte name field has two syntactic forms. A nonzero first four-byte
word begins an inline name; a zero word selects a 32-bit string-table offset in
the second half. Offset range and terminating-string checks require the
surrounding string table and therefore remain contextual validation obligations.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- The two syntactic interpretations of an eight-byte COFF symbol name.
`inline` retains both raw 32-bit halves and proves the discriminator nonzero. -/
inductive SymbolName where
  | inline (first second : BitVec 32)
      (notStringTableMarker : first ≠ (0 : BitVec 32))
  | stringTableOffset (offset : BitVec 32)
deriving DecidableEq, Repr

/-- The two little-endian words present in the raw name field. -/
abbrev SymbolNameWords := BitVec 32 × BitVec 32

/-- Convert typed name syntax back to its exact pair of raw words. -/
def SymbolName.toWords : SymbolName → SymbolNameWords
  | .inline first second _ => (first, second)
  | .stringTableOffset offset => (0, offset)

/-- Classify raw words by the zero marker in the first word. -/
def SymbolName.ofWords (words : SymbolNameWords) : SymbolName :=
  if marker : words.1 = (0 : BitVec 32) then
    .stringTableOffset words.2
  else
    .inline words.1 words.2 marker

/-- Classifying the words emitted for a typed name returns that exact name. -/
@[simp] theorem SymbolName.ofWords_toWords (name : SymbolName) :
    SymbolName.ofWords name.toWords = name := by
  cases name with
  | inline first second notMarker =>
      unfold SymbolName.toWords SymbolName.ofWords
      simp only
      split
      next marker => contradiction
      next => rfl
  | stringTableOffset offset =>
      simp [SymbolName.toWords, SymbolName.ofWords]

/-- `SymbolName.toWords_ofWords` states that re-emitting either classification
preserves both raw words exactly. -/
@[simp] theorem SymbolName.toWords_ofWords (words : SymbolNameWords) :
    (SymbolName.ofWords words).toWords = words := by
  rcases words with ⟨first, second⟩
  unfold SymbolName.ofWords
  split
  next marker =>
    change first = 0 at marker
    subst first
    rfl
  next => rfl

/-- Raw word pairs and their disjoint typed syntax are isomorphic. -/
def symbolNameIsomorphism : Isomorphism SymbolNameWords SymbolName where
  forward := SymbolName.ofWords
  backward := SymbolName.toWords
  backward_forward := SymbolName.toWords_ofWords
  forward_backward := SymbolName.ofWords_toWords

/-- Generic grammar for the two little-endian words in a symbol name. -/
def symbolNameWordsFormat : Format SymbolNameWords :=
  .seq littleEndianU32Format fun _ => littleEndianU32Format

/-- Typed COFF symbol-name grammar. -/
def symbolNameFormat : Format SymbolName :=
  symbolNameWordsFormat.iso symbolNameIsomorphism

/-- Decode one typed name after its eight-byte bound is established. -/
private def readCompleteSymbolName
    (input : Std.Logical.ByteArray) : ParseResult SymbolName :=
  match takeLittleEndian 4 input with
  | .done first rest =>
    match takeLittleEndian 4 rest with
    | .done second rest => .done (SymbolName.ofWords (first, second)) rest
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse and classify one eight-byte COFF symbol-name field. -/
def readSymbolName (input : Std.Logical.ByteArray) : ParseResult SymbolName :=
  if 8 ≤ input.length then
    readCompleteSymbolName input
  else
    .needMore (some (8 - input.length))

/-- A short name field reports its exact whole-field deficit. -/
theorem readSymbolName_short {input : Std.Logical.ByteArray}
    (short : input.length < 8) :
    readSymbolName input = .needMore (some (8 - input.length)) := by
  simp [readSymbolName, Nat.not_le.mpr short]

/-- Serialize a typed symbol name into its canonical eight-byte field. -/
def writeSymbolName (name : SymbolName) : Std.Logical.ByteArray :=
  let words := name.toWords
  writeLittleEndian (count := 4) words.1 ++
    writeLittleEndian (count := 4) words.2

/-- Every typed symbol-name serialization is exactly eight bytes. -/
@[simp] theorem length_writeSymbolName (name : SymbolName) :
    (writeSymbolName name).length = 8 := by
  simp [writeSymbolName, writeLittleEndian, isoWriter, writeExact]

/-- Every typed symbol-name serialization derives from its declared grammar. -/
theorem writeSymbolName_derives (name : SymbolName) :
    Derives symbolNameFormat (writeSymbolName name) name Vec.empty := by
  unfold symbolNameFormat
  have inner : Derives symbolNameWordsFormat (writeSymbolName name)
      name.toWords Vec.empty := by
    unfold symbolNameWordsFormat writeSymbolName
    exact Derives.seqAppend
      ((writeLittleEndian_realizes 4).sound name.toWords.1)
      ((writeLittleEndian_realizes 4).sound name.toWords.2)
  have outer := @Derives.iso SymbolNameWords SymbolName symbolNameWordsFormat
    symbolNameIsomorphism (writeSymbolName name) Vec.empty name.toWords inner
  have valueEq : symbolNameIsomorphism.forward name.toWords = name :=
    SymbolName.ofWords_toWords name
  rw [valueEq] at outer
  exact outer

/-- Typed symbol names round-trip while preserving any following suffix. -/
@[simp] theorem readSymbolName_writeSymbolName_append
    (name : SymbolName) (rest : Std.Logical.ByteArray) :
    readSymbolName (writeSymbolName name ++ rest) = .done name rest := by
  simp only [readSymbolName, Vec.length_append, length_writeSymbolName]
  have enough : 8 ≤ 8 + rest.length := by omega
  simp only [enough, ite_true]
  simp only [readCompleteSymbolName, writeSymbolName, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]
  rw [SymbolName.ofWords_toWords]

/-- Whole-field typed symbol-name round trip. -/
@[simp] theorem readSymbolName_writeSymbolName (name : SymbolName) :
    readSymbolName (writeSymbolName name) = .done name Vec.empty := by
  simpa using readSymbolName_writeSymbolName_append name Vec.empty

/-! ## Primary symbol records -/

/-- A primary COFF symbol record with its name syntax already classified.
Auxiliary cells continue to use the lossless `SymbolCell` representation. -/
structure Symbol where
  name : SymbolName
  value : BitVec 32
  sectionNumber : BitVec 16
  symbolType : BitVec 16
  storageClass : Byte
  numberOfAuxSymbols : Byte
deriving DecidableEq, Repr

/-- Product shape used by the primary-symbol grammar. -/
abbrev SymbolFields :=
  SymbolName × BitVec 32 × BitVec 16 × BitVec 16 × Byte × Byte

/-- Forget primary-symbol field labels without losing any value. -/
def Symbol.toFields (symbol : Symbol) : SymbolFields :=
  (symbol.name, symbol.value, symbol.sectionNumber, symbol.symbolType,
    symbol.storageClass, symbol.numberOfAuxSymbols)

/-- Restore a named primary symbol from its grammar product. -/
def Symbol.ofFields (fields : SymbolFields) : Symbol where
  name := fields.1
  value := fields.2.1
  sectionNumber := fields.2.2.1
  symbolType := fields.2.2.2.1
  storageClass := fields.2.2.2.2.1
  numberOfAuxSymbols := fields.2.2.2.2.2

/-- Primary symbols and their grammar products are totally isomorphic. -/
def symbolFieldsIsomorphism : Isomorphism SymbolFields Symbol where
  forward := Symbol.ofFields
  backward := Symbol.toFields
  backward_forward := by intro fields; rcases fields with ⟨a,b,c,d,e,f⟩; rfl
  forward_backward := by intro symbol; rcases symbol with ⟨a,b,c,d,e,f⟩; rfl

/-- Generic grammar for a primary symbol with a classified name. -/
def symbolFieldsFormat : Format SymbolFields :=
  .seq symbolNameFormat fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq anyByteFormat fun _ =>
  anyByteFormat

/-- Typed language of one primary COFF symbol record. -/
def symbolFormat : Format Symbol :=
  symbolFieldsFormat.iso symbolFieldsIsomorphism

/-- Decode a typed primary symbol after its 18-byte bound is established. -/
private def readCompleteSymbol
    (input : Std.Logical.ByteArray) : ParseResult Symbol :=
  match readSymbolName input with
  | .done name rest =>
    match takeLittleEndian 4 rest with
    | .done value rest =>
      match takeLittleEndian 2 rest with
      | .done sectionNumber rest =>
        match takeLittleEndian 2 rest with
        | .done symbolType rest =>
          match takeByte rest with
          | .done storageClass rest =>
            match takeByte rest with
            | .done numberOfAuxSymbols rest => .done {
                name, value, sectionNumber, symbolType,
                storageClass, numberOfAuxSymbols } rest
            | .needMore hint => .needMore hint
            | .invalid error => .invalid error
          | .needMore hint => .needMore hint
          | .invalid error => .invalid error
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse one typed primary symbol with exact whole-record deficit reporting. -/
def readSymbol (input : Std.Logical.ByteArray) : ParseResult Symbol :=
  if 18 ≤ input.length then readCompleteSymbol input
  else .needMore (some (18 - input.length))

/-- A truncated primary symbol reports its exact missing byte count. -/
theorem readSymbol_short {input : Std.Logical.ByteArray}
    (short : input.length < 18) :
    readSymbol input = .needMore (some (18 - input.length)) := by
  simp [readSymbol, Nat.not_le.mpr short]

/-- Serialize a typed primary symbol in canonical field order. -/
def writeSymbol (symbol : Symbol) : Std.Logical.ByteArray :=
  writeSymbolName symbol.name ++
  writeLittleEndian (count := 4) symbol.value ++
  writeLittleEndian (count := 2) symbol.sectionNumber ++
  writeLittleEndian (count := 2) symbol.symbolType ++
  writeByte symbol.storageClass ++ writeByte symbol.numberOfAuxSymbols

/-- Typed primary-symbol serializations occupy exactly 18 bytes. -/
@[simp] theorem length_writeSymbol (symbol : Symbol) :
    (writeSymbol symbol).length = 18 := by
  simp [writeSymbol, writeLittleEndian, isoWriter, writeExact, writeByte]

/-- Every typed primary-symbol serialization derives from its grammar. -/
theorem writeSymbol_derives (symbol : Symbol) :
    Derives symbolFormat (writeSymbol symbol) symbol Vec.empty := by
  rcases symbol with ⟨name, value, sectionNumber, symbolType, storage, auxiliary⟩
  unfold symbolFormat
  refine @Derives.iso SymbolFields Symbol symbolFieldsFormat
    symbolFieldsIsomorphism _ Vec.empty
    (name, value, sectionNumber, symbolType, storage, auxiliary) ?_
  simp only [writeSymbol, Vec.append_assoc]
  unfold symbolFieldsFormat littleEndianU16Format littleEndianU32Format
  exact Derives.seqAppend (writeSymbolName_derives name)
    (Derives.seqAppend ((writeLittleEndian_realizes 4).sound value)
      (Derives.seqAppend ((writeLittleEndian_realizes 2).sound sectionNumber)
        (Derives.seqAppend ((writeLittleEndian_realizes 2).sound symbolType)
          (Derives.seqAppend (writeByte_realizes.sound storage)
            (writeByte_realizes.sound auxiliary)))))

/-- Typed primary symbols round-trip with exact suffix preservation. -/
@[simp] theorem readSymbol_writeSymbol_append
    (symbol : Symbol) (rest : Std.Logical.ByteArray) :
    readSymbol (writeSymbol symbol ++ rest) = .done symbol rest := by
  rcases symbol with ⟨name, value, sectionNumber, symbolType, storage, auxiliary⟩
  simp only [readSymbol, Vec.length_append, length_writeSymbol]
  have enough : 18 ≤ 18 + rest.length := by omega
  simp only [enough, ite_true]
  simp only [readCompleteSymbol, writeSymbol, Vec.append_assoc,
    readSymbolName_writeSymbolName_append,
    takeLittleEndian_writeLittleEndian_append, takeByte_writeByte_append]

/-- Whole-record typed primary-symbol round trip. -/
@[simp] theorem readSymbol_writeSymbol (symbol : Symbol) :
    readSymbol (writeSymbol symbol) = .done symbol Vec.empty := by
  simpa using readSymbol_writeSymbol_append symbol Vec.empty

end Grass.Artifact.COFF
