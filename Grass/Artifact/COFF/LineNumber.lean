import Grass.Artifact.COFF.SymbolValidation

/-!
# COFF line-number records

The six-byte COFF line-number union uses a zero 16-bit line number to select a
function symbol-table index; nonzero values select a virtual-address/source-line
pair. This module models that disjoint syntax and section-declared record counts,
without assigning source-language or debugger semantics.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Disjoint typed interpretations of the COFF line-number union. -/
inductive LineNumber where
  | functionSymbolIndex (symbolTableIndex : BitVec 32)
  | sourceLine (virtualAddress : BitVec 32) (line : BitVec 16)
      (lineNonzero : line ≠ (0 : BitVec 16))
deriving DecidableEq, Repr

/-- The raw 32-bit union word and 16-bit discriminator/value. -/
abbrev LineNumberFields := BitVec 32 × BitVec 16

/-- Convert typed line-number syntax to its exact raw fields. -/
def LineNumber.toFields : LineNumber → LineNumberFields
  | .functionSymbolIndex index => (index, 0)
  | .sourceLine address line _ => (address, line)

/-- Classify raw fields by the zero line-number discriminator. -/
def LineNumber.ofFields (fields : LineNumberFields) : LineNumber :=
  if zero : fields.2 = (0 : BitVec 16) then
    .functionSymbolIndex fields.1
  else
    .sourceLine fields.1 fields.2 zero

/-- Classifying the fields emitted for typed line syntax returns that syntax. -/
@[simp] theorem LineNumber.ofFields_toFields (line : LineNumber) :
    LineNumber.ofFields line.toFields = line := by
  cases line with
  | functionSymbolIndex index => simp [LineNumber.ofFields, LineNumber.toFields]
  | sourceLine address number nonzero =>
      unfold LineNumber.ofFields LineNumber.toFields
      simp only
      split
      next zero => contradiction
      next => rfl

/-- `LineNumber.toFields_ofFields` preserves both raw fields exactly. -/
@[simp] theorem LineNumber.toFields_ofFields (fields : LineNumberFields) :
    (LineNumber.ofFields fields).toFields = fields := by
  rcases fields with ⟨word, number⟩
  unfold LineNumber.ofFields
  split
  next zero =>
    change number = 0 at zero
    subst number
    rfl
  next => rfl

/-- Raw and typed line-number representations are totally isomorphic. -/
def lineNumberIsomorphism : Isomorphism LineNumberFields LineNumber where
  forward := LineNumber.ofFields
  backward := LineNumber.toFields
  backward_forward := LineNumber.toFields_ofFields
  forward_backward := LineNumber.ofFields_toFields

/-- Generic grammar for the two little-endian line-number fields. -/
def lineNumberFieldsFormat : Format LineNumberFields :=
  .seq littleEndianU32Format fun _ => littleEndianU16Format

/-- Typed language of one six-byte COFF line-number record. -/
def lineNumberFormat : Format LineNumber :=
  lineNumberFieldsFormat.iso lineNumberIsomorphism

/-- Decode one line-number union after its six-byte bound is established. -/
private def readCompleteLineNumber
    (input : Std.Logical.ByteArray) : ParseResult LineNumber :=
  match takeLittleEndian 4 input with
  | .done word rest =>
    match takeLittleEndian 2 rest with
    | .done number rest => .done (LineNumber.ofFields (word, number)) rest
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse and classify one fixed-width COFF line-number record. -/
def readLineNumber (input : Std.Logical.ByteArray) : ParseResult LineNumber :=
  if 6 ≤ input.length then readCompleteLineNumber input
  else .needMore (some (6 - input.length))

/-- A short line-number record reports its exact whole-record deficit. -/
theorem readLineNumber_short {input : Std.Logical.ByteArray}
    (short : input.length < 6) :
    readLineNumber input = .needMore (some (6 - input.length)) := by
  simp [readLineNumber, Nat.not_le.mpr short]

/-- Serialize typed line-number syntax into its canonical six-byte record. -/
def writeLineNumber (line : LineNumber) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) line.toFields.1 ++
  writeLittleEndian (count := 2) line.toFields.2

/-- Every canonical line-number serialization is exactly six bytes. -/
@[simp] theorem length_writeLineNumber (line : LineNumber) :
    (writeLineNumber line).length = 6 := by
  simp [writeLineNumber, writeLittleEndian, isoWriter, writeExact]

/-- Every canonical line-number serialization derives from its typed grammar. -/
theorem writeLineNumber_derives (line : LineNumber) :
    Derives lineNumberFormat (writeLineNumber line) line Vec.empty := by
  unfold lineNumberFormat
  have inner : Derives lineNumberFieldsFormat (writeLineNumber line)
      line.toFields Vec.empty := by
    unfold lineNumberFieldsFormat writeLineNumber
    exact Derives.seqAppend
      ((writeLittleEndian_realizes 4).sound line.toFields.1)
      ((writeLittleEndian_realizes 2).sound line.toFields.2)
  have outer := @Derives.iso LineNumberFields LineNumber lineNumberFieldsFormat
    lineNumberIsomorphism (writeLineNumber line) Vec.empty line.toFields inner
  have valueEq : lineNumberIsomorphism.forward line.toFields = line :=
    LineNumber.ofFields_toFields line
  rw [valueEq] at outer
  exact outer

/-- Canonical line-number records round-trip with exact suffix preservation. -/
@[simp] theorem readLineNumber_writeLineNumber_append
    (line : LineNumber) (rest : Std.Logical.ByteArray) :
    readLineNumber (writeLineNumber line ++ rest) = .done line rest := by
  simp only [readLineNumber, Vec.length_append, length_writeLineNumber]
  have enough : 6 ≤ 6 + rest.length := by omega
  simp only [enough, ite_true]
  simp only [readCompleteLineNumber, writeLineNumber, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]
  rw [LineNumber.ofFields_toFields]

/-- Whole-record canonical line-number round trip. -/
@[simp] theorem readLineNumber_writeLineNumber (line : LineNumber) :
    readLineNumber (writeLineNumber line) = .done line Vec.empty := by
  simpa using readLineNumber_writeLineNumber_append line Vec.empty

/-! ## Section-declared line-number blocks -/

/-- Recursive serializer beneath the ordered block writer. -/
private def writeLineNumberList : List LineNumber → Std.Logical.ByteArray
  | [] => Vec.empty
  | line :: rest => writeLineNumber line ++ writeLineNumberList rest

/-- Serialize ordered line-number records. -/
def writeLineNumbers (lines : Vec LineNumber) : Std.Logical.ByteArray :=
  writeLineNumberList lines.toList

/-- Consing one record emits it before the remaining block. -/
@[simp] theorem writeLineNumbers_cons (line : LineNumber)
    (rest : Vec LineNumber) :
    writeLineNumbers (Vec.singleton line ++ rest) =
      writeLineNumber line ++ writeLineNumbers rest := by
  rfl

/-- Ordered line-number blocks occupy six bytes per entry. -/
@[simp] theorem length_writeLineNumbers (lines : Vec LineNumber) :
    (writeLineNumbers lines).length = 6 * lines.length := by
  induction lines using Vec.recOnCons with
  | empty => rfl
  | cons line rest ih =>
      rw [writeLineNumbers_cons, Vec.length_append, length_writeLineNumber, ih]
      simp [Nat.mul_add]

/-- Parse exactly `count` ordered line-number records. -/
def readLineNumbers :
    (count : Nat) → Std.Logical.ByteArray → ParseResult (Vec LineNumber)
  | 0, input => .done Vec.empty input
  | count + 1, input =>
    match readLineNumber input with
    | .done line rest =>
      match readLineNumbers count rest with
      | .done lines suffix => .done (Vec.singleton line ++ lines) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- Successful bounded parsing returns the requested line-number count. -/
theorem readLineNumbers_done_length {count : Nat} {input lines rest}
    (success : readLineNumbers count input = .done lines rest) :
    lines.length = count := by
  induction count generalizing input lines rest with
  | zero =>
      simp only [readLineNumbers] at success
      injection success with linesEq
      rw [← linesEq]
      simp
  | succ count ih =>
      simp only [readLineNumbers] at success
      split at success <;> try contradiction
      next line suffix parsedLine =>
        split at success <;> try contradiction
        next tail final parsedTail =>
          injection success with linesEq restEq
          rw [← linesEq, Vec.length_append]
          simp only [Vec.length_singleton]
          rw [ih parsedTail]
          omega

/-- Ordered line-number vectors round-trip with exact suffix preservation. -/
@[simp] theorem readLineNumbers_writeLineNumbers_append
    (lines : Vec LineNumber) (rest : Std.Logical.ByteArray) :
    readLineNumbers lines.length (writeLineNumbers lines ++ rest) =
      .done lines rest := by
  induction lines using Vec.recOnCons generalizing rest with
  | empty =>
      change readLineNumbers 0 (Vec.empty ++ rest) = .done Vec.empty rest
      simp [readLineNumbers]
  | cons line tail ih =>
      rw [writeLineNumbers_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add, Vec.append_assoc,
        readLineNumbers]
      rw [readLineNumber_writeLineNumber_append]
      simp only
      rw [ih rest]

/-- Every serialized line-number vector derives from its repetition grammar. -/
theorem writeLineNumbers_derives (lines : Vec LineNumber) :
    Derives (.repeat lines.length lineNumberFormat)
      (writeLineNumbers lines) lines Vec.empty := by
  induction lines using Vec.recOnCons with
  | empty => exact Derives.repeatZero lineNumberFormat Vec.empty
  | cons line tail ih =>
      rw [writeLineNumbers_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add]
      exact Derives.repeatSucc
        ((writeLineNumber_derives line).appendSuffix (writeLineNumbers tail)) ih

/-- A line-number vector coupled to one section header's declared count. -/
structure LineNumberBlock (sectionHeader : SectionHeader) where
  lines : Vec LineNumber
  lineCount : lines.length = sectionHeader.numberOfLineNumbers.toNat
deriving DecidableEq, Repr

/-- Proof-bearing vector representation used by grammar refinement. -/
abbrev CheckedLineNumberBlock (sectionHeader : SectionHeader) :=
  {lines : Vec LineNumber //
    lines.length = sectionHeader.numberOfLineNumbers.toNat}

/-- Convert a checked vector into the named block wrapper. -/
def LineNumberBlock.ofChecked {sectionHeader : SectionHeader}
    (block : CheckedLineNumberBlock sectionHeader) :
    LineNumberBlock sectionHeader where
  lines := block.1
  lineCount := block.2

/-- Convert the named wrapper back to its checked vector. -/
def LineNumberBlock.toChecked {sectionHeader : SectionHeader}
    (block : LineNumberBlock sectionHeader) :
    CheckedLineNumberBlock sectionHeader := ⟨block.lines, block.lineCount⟩

/-- Named and subtype line-number blocks are totally isomorphic. -/
def lineNumberBlockIsomorphism (sectionHeader : SectionHeader) :
    Isomorphism (CheckedLineNumberBlock sectionHeader)
      (LineNumberBlock sectionHeader) where
  forward := LineNumberBlock.ofChecked
  backward := LineNumberBlock.toChecked
  backward_forward := by intro block; rcases block with ⟨lines, count⟩; rfl
  forward_backward := by intro block; rcases block with ⟨lines, count⟩; rfl

/-- Count-refined grammar for one section's line-number block. -/
def checkedLineNumberBlockFormat (sectionHeader : SectionHeader) :
    Format (CheckedLineNumberBlock sectionHeader) :=
  (Format.repeat sectionHeader.numberOfLineNumbers.toNat
    lineNumberFormat).refineValue fun lines =>
      lines.length = sectionHeader.numberOfLineNumbers.toNat

/-- Typed line-number block language coupled to a section header. -/
def lineNumberBlockFormat (sectionHeader : SectionHeader) :
    Format (LineNumberBlock sectionHeader) :=
  (checkedLineNumberBlockFormat sectionHeader).iso
    (lineNumberBlockIsomorphism sectionHeader)

/-- Parse a section's complete declared line-number block after exact preflight. -/
def readLineNumberBlock (sectionHeader : SectionHeader)
    (input : Std.Logical.ByteArray) : ParseResult (LineNumberBlock sectionHeader) :=
  let required := 6 * sectionHeader.numberOfLineNumbers.toNat
  if required ≤ input.length then
    match readLineNumbers sectionHeader.numberOfLineNumbers.toNat input with
    | .done lines rest =>
      if count : lines.length = sectionHeader.numberOfLineNumbers.toNat then
        .done { lines, lineCount := count } rest
      else .invalid (.malformed "line-number block count mismatch")
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else .needMore (some (required - input.length))

/-- Serialize a section-count-coupled line-number block. -/
def writeLineNumberBlock {sectionHeader : SectionHeader}
    (block : LineNumberBlock sectionHeader) : Std.Logical.ByteArray :=
  writeLineNumbers block.lines

/-- A coupled block occupies six bytes times its section-declared count. -/
@[simp] theorem length_writeLineNumberBlock {sectionHeader : SectionHeader}
    (block : LineNumberBlock sectionHeader) :
    (writeLineNumberBlock block).length =
      6 * sectionHeader.numberOfLineNumbers.toNat := by
  simp [writeLineNumberBlock, block.lineCount]

/-- Coupled line-number blocks round-trip with exact suffix preservation. -/
@[simp] theorem readLineNumberBlock_write_append {sectionHeader : SectionHeader}
    (block : LineNumberBlock sectionHeader) (rest : Std.Logical.ByteArray) :
    readLineNumberBlock sectionHeader (writeLineNumberBlock block ++ rest) =
      .done block rest := by
  rcases block with ⟨lines, count⟩
  simp only [readLineNumberBlock, writeLineNumberBlock, Vec.length_append,
    length_writeLineNumbers]
  have enough : 6 * sectionHeader.numberOfLineNumbers.toNat ≤
      6 * lines.length + rest.length := by simp [count]
  simp only [enough, ite_true]
  have parsed : readLineNumbers sectionHeader.numberOfLineNumbers.toNat
      (writeLineNumbers lines ++ rest) = .done lines rest := by
    simpa only [← count] using readLineNumbers_writeLineNumbers_append lines rest
  rw [parsed]
  simp only [count, ↓reduceDIte]

/-- Every coupled block serialization derives from its count-refined grammar. -/
theorem writeLineNumberBlock_derives {sectionHeader : SectionHeader}
    (block : LineNumberBlock sectionHeader) :
    Derives (lineNumberBlockFormat sectionHeader)
      (writeLineNumberBlock block) block Vec.empty := by
  rcases block with ⟨lines, count⟩
  unfold lineNumberBlockFormat
  refine @Derives.iso (CheckedLineNumberBlock sectionHeader)
    (LineNumberBlock sectionHeader) (checkedLineNumberBlockFormat sectionHeader)
    (lineNumberBlockIsomorphism sectionHeader) _ Vec.empty ⟨lines, count⟩ ?_
  unfold checkedLineNumberBlockFormat
  apply Derives.lift
  simpa only [writeLineNumberBlock, count] using writeLineNumbers_derives lines

end Grass.Artifact.COFF
