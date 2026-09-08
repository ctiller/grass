import Grass.Artifact.Binary.Gobj.ImportManifest
import Grass.Artifact.Binary.Gobj.Section

/-!
# Typed `.gobj` symbol entries

This layer gives the proof-free symbol table a canonical binary realization.
`GobjSymbolTable` carries unique names, while `readGobjSymbol` checks bindings,
reserved bits, and section-relative extents against the 64-bit object domain.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Linkage visibility carried by a serialized `.gobj` symbol. -/
inductive GobjSymbolBinding where
  | local
  | exported
deriving DecidableEq, Repr

/-- Canonical one-byte realization of a symbol binding. -/
def GobjSymbolBinding.toByte : GobjSymbolBinding → Byte
  | .local => 0
  | .exported => 1

/-- Decode a symbol binding and reject all unassigned byte values. -/
def readGobjSymbolBinding (bits : Byte) : Except ParseError GobjSymbolBinding :=
  if bits = 0 then .ok .local
  else if bits = 1 then .ok .exported
  else .error (.malformed "invalid .gobj symbol binding")

/-- `readGobjSymbolBinding_toByte` inverts the canonical binding realization. -/
@[simp] theorem readGobjSymbolBinding_toByte (binding : GobjSymbolBinding) :
    readGobjSymbolBinding binding.toByte = .ok binding := by
  cases binding <;> rfl

/-- Section-relative definition carried only by a defined symbol. -/
structure GobjDefinedSymbol where
  binding : GobjSymbolBinding
  sectionIndex : BitVec 32
  offset : BitVec 64
  size : BitVec 64
  extentFits : offset.toNat + size.toNat ≤ 2 ^ 64
deriving DecidableEq, Repr

/-- A symbol is either section-defined or an index into the import manifest. -/
inductive GobjSymbolBody where
  | defined (definition : GobjDefinedSymbol)
  | imported (importIndex : BitVec 32)
deriving DecidableEq, Repr

/-- One uniformly indexed relocation target. -/
structure GobjSymbol where
  name : GobjNominalId
  body : GobjSymbolBody
deriving DecidableEq, Repr

/-- Serialize one canonical symbol entry. -/
def writeGobjSymbol (entry : GobjSymbol) : Std.Logical.ByteArray :=
  writeGobjNominalId entry.name ++ (match entry.body with
  | .defined definition =>
    writeByte definition.binding.toByte ++
    writeLittleEndian (count := 3) (0 : BitVec 24) ++
    writeLittleEndian (count := 4) definition.sectionIndex ++
    writeLittleEndian (count := 8) definition.offset ++
    writeLittleEndian (count := 8) definition.size
  | .imported importIndex =>
    writeByte 2 ++ writeLittleEndian (count := 3) (0 : BitVec 24) ++
      writeLittleEndian (count := 4) importIndex)

/-- Parse one symbol entry while retaining the exact unconsumed suffix. Binding
tags are rejected before reading later reserved bytes. -/
def readGobjSymbol (input : Std.Logical.ByteArray) : ParseResult GobjSymbol :=
  match readGobjNominalId input with
  | .done name afterName =>
    match takeByte afterName with
    | .done bindingBits afterBinding =>
      if bindingBits = 2 then
        match takeLittleEndian 3 afterBinding with
        | .done reserved afterReserved =>
          if _reservedOk : reserved = 0 then
            match takeLittleEndian 4 afterReserved with
            | .done importIndex suffix =>
              .done { name, body := .imported importIndex } suffix
            | .needMore hint => .needMore hint
            | .invalid error => .invalid error
          else .invalid (.malformed "nonzero .gobj symbol reserved field")
        | .needMore hint => requireAfter 4 (.needMore hint)
        | .invalid error => .invalid error
      else
        match readGobjSymbolBinding bindingBits with
        | .ok binding =>
          match takeLittleEndian 3 afterBinding with
          | .done reserved afterReserved =>
            if _reservedOk : reserved = 0 then
              match takeLittleEndian 4 afterReserved with
              | .done sectionIndex afterSectionIndex =>
                match takeLittleEndian 8 afterSectionIndex with
                | .done offset afterOffset =>
                  match takeLittleEndian 8 afterOffset with
                  | .done size suffix =>
                    if extentFits : offset.toNat + size.toNat ≤ 2 ^ 64 then
                      .done { name, body := .defined {
                        binding, sectionIndex, offset, size, extentFits } } suffix
                    else
                      .invalid (.malformed
                        ".gobj symbol extent overflows 64 bits")
                  | .needMore hint => .needMore hint
                  | .invalid error => .invalid error
                | .needMore hint => requireAfter 8 (.needMore hint)
                | .invalid error => .invalid error
              | .needMore hint => requireAfter 16 (.needMore hint)
              | .invalid error => .invalid error
            else .invalid (.malformed "nonzero .gobj symbol reserved field")
          | .needMore hint => requireAfter 20 (.needMore hint)
          | .invalid error => .invalid error
        | .error error => .invalid error
    | .needMore hint => requireAfter 7 (.needMore hint)
    | .invalid error => .invalid error
  | .needMore hint => requireAfter 8 (.needMore hint)
  | .invalid error => .invalid error

/-- `length_writeGobjSymbol` gives the exact symbol-entry width. -/
@[simp] theorem length_writeGobjSymbol (entry : GobjSymbol) :
    (writeGobjSymbol entry).length = (writeGobjNominalId entry.name).length +
      match entry.body with | .defined _ => 24 | .imported _ => 8 := by
  cases entry with
  | mk name body =>
      cases body <;> simp [writeGobjSymbol, writeGobjNominalId, writeByte] <;>
        omega

/-- `readGobjSymbol_write_append` parses one canonical symbol exactly and
preserves every following suffix. -/
@[simp] theorem readGobjSymbol_write_append (entry : GobjSymbol)
    (suffix : Std.Logical.ByteArray) :
    readGobjSymbol (writeGobjSymbol entry ++ suffix) = .done entry suffix := by
  unfold readGobjSymbol writeGobjSymbol
  cases entry with
  | mk name body =>
    cases body with
    | defined definition =>
        simp only [Vec.append_assoc]
        rw [readGobjNominalId_write_append]
        simp only
        rw [takeByte_writeByte_append]
        simp only
        rw [takeLittleEndian_writeLittleEndian_append]
        simp only [dite_true]
        rw [if_neg (by cases definition.binding <;> decide :
          definition.binding.toByte ≠ 2)]
        simp only [readGobjSymbolBinding_toByte]
        rw [takeLittleEndian_writeLittleEndian_append]
        simp only
        rw [takeLittleEndian_writeLittleEndian_append]
        simp only
        rw [takeLittleEndian_writeLittleEndian_append]
        simp only
        rw [dif_pos definition.extentFits]
    | imported importIndex =>
        simp only [Vec.append_assoc]
        rw [readGobjNominalId_write_append]
        simp only
        rw [takeByte_writeByte_append]
        simp only
        rw [takeLittleEndian_writeLittleEndian_append]
        simp only [dite_true, ite_true]
        rw [takeLittleEndian_writeLittleEndian_append]

/-- `readGobjSymbol_write` is the complete-input symbol round trip. -/
@[simp] theorem readGobjSymbol_write (entry : GobjSymbol) :
    readGobjSymbol (writeGobjSymbol entry) = .done entry Vec.empty := by
  simpa using readGobjSymbol_write_append entry Vec.empty

/-- Serialize symbol entries consecutively in canonical source order. -/
def writeGobjSymbolList : List GobjSymbol → Std.Logical.ByteArray
  | [] => Vec.empty
  | entry :: entries => writeGobjSymbol entry ++ writeGobjSymbolList entries

/-- Total canonical byte width of a symbol-entry list. -/
def gobjSymbolListLength : List GobjSymbol → Nat
  | [] => 0
  | entry :: entries =>
    (writeGobjNominalId entry.name).length +
      (match entry.body with | .defined _ => 24 | .imported _ => 8) +
      gobjSymbolListLength entries

/-- The recursive symbol-list writer has its exact declared width. -/
@[simp] theorem length_writeGobjSymbolList (entries : List GobjSymbol) :
    (writeGobjSymbolList entries).length = gobjSymbolListLength entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp [writeGobjSymbolList, gobjSymbolListLength, ih]

/-- `minLength_gobjSymbolList` bounds each encoded symbol by 16 bytes. -/
theorem minLength_gobjSymbolList (entries : List GobjSymbol) :
    16 * entries.length ≤ gobjSymbolListLength entries := by
  induction entries with
  | nil => simp [gobjSymbolListLength]
  | cons entry entries ih =>
      simp only [List.length_cons, gobjSymbolListLength]
      have nameMinimum := minLength_writeGobjNominalId entry.name
      cases entry.body <;> simp_all <;> omega

/-- Parse exactly `count` consecutive symbol entries. -/
def readGobjSymbolList : Nat → Std.Logical.ByteArray →
    ParseResult (List GobjSymbol)
  | 0, input => .done [] input
  | count + 1, input =>
    match readGobjSymbol input with
    | .done entry rest =>
      match readGobjSymbolList count rest with
      | .done entries suffix => .done (entry :: entries) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => requireAfter (16 * count) (.needMore hint)
    | .invalid error => .invalid error

/-- `readGobjSymbolList_write_append` parses a canonical symbol list exactly
and preserves an arbitrary suffix. -/
@[simp] theorem readGobjSymbolList_write_append (entries : List GobjSymbol)
    (suffix : Std.Logical.ByteArray) :
    readGobjSymbolList entries.length (writeGobjSymbolList entries ++ suffix) =
      .done entries suffix := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.length_cons, writeGobjSymbolList, Vec.append_assoc,
        readGobjSymbolList]
      rw [readGobjSymbol_write_append]
      simp only
      rw [ih]

/-- A count-representable symbol table whose serialized names are unique. -/
structure GobjSymbolTable where
  entries : Vec GobjSymbol
  countFits : entries.length < 2 ^ 32
  namesUnique : (entries.toList.map fun entry => entry.name).Nodup
deriving DecidableEq, Repr

/-- Serialize a symbol count and all canonical entries. -/
def writeGobjSymbolTable (table : GobjSymbolTable) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (BitVec.ofNat 32 table.entries.length) ++
    writeGobjSymbolList table.entries.toList

/-- Parse a symbol table, rejecting impossible counts and duplicate names. -/
def readGobjSymbolTable (input : Std.Logical.ByteArray) :
    ParseResult GobjSymbolTable :=
  match takeLittleEndian 4 input with
  | .done count rest =>
    match readGobjSymbolList count.toNat rest with
    | .done entries suffix =>
      if countExact : entries.length = count.toNat then
        if namesUnique : (entries.map fun entry => entry.name).Nodup then
          .done {
            entries := Vec.fromList entries
            countFits := by
              simp only [Vec.length_fromList, countExact]
              simpa using BitVec.isLt count
            namesUnique := by simpa using namesUnique } suffix
        else
          .invalid (.malformed "duplicate .gobj symbol name")
      else
        .invalid (.malformed ".gobj symbol-count mismatch")
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- `length_writeGobjSymbolTable` gives the table's exact encoded width. -/
@[simp] theorem length_writeGobjSymbolTable (table : GobjSymbolTable) :
    (writeGobjSymbolTable table).length =
      4 + gobjSymbolListLength table.entries.toList := by
  simp [writeGobjSymbolTable]

/-- `readGobjSymbolTable_write_append` parses a canonical typed symbol table
exactly and preserves every following suffix. -/
@[simp] theorem readGobjSymbolTable_write_append (table : GobjSymbolTable)
    (suffix : Std.Logical.ByteArray) :
    readGobjSymbolTable (writeGobjSymbolTable table ++ suffix) =
      .done table suffix := by
  have countEq : (BitVec.ofNat 32 table.entries.length).toNat =
      table.entries.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt table.countFits]
  have parsedEntries :
      readGobjSymbolList (BitVec.ofNat 32 table.entries.length).toNat
          (writeGobjSymbolList table.entries.toList ++ suffix) =
        .done table.entries.toList suffix := by
    rw [countEq]
    exact readGobjSymbolList_write_append table.entries.toList suffix
  have countExact : table.entries.toList.length =
      (BitVec.ofNat 32 table.entries.length).toNat := by
    rw [countEq]
    rfl
  unfold readGobjSymbolTable writeGobjSymbolTable
  rw [Vec.append_assoc, takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [parsedEntries]
  simp only
  rw [dif_pos countExact]
  rw [dif_pos table.namesUnique]

/-- The whole symbol-table round trip is the empty-suffix specialization. -/
@[simp] theorem readGobjSymbolTable_write (table : GobjSymbolTable) :
    readGobjSymbolTable (writeGobjSymbolTable table) =
      .done table Vec.empty := by
  simpa using readGobjSymbolTable_write_append table Vec.empty

/-- Embed a typed symbol table into the envelope's checked byte framing. -/
def GobjSymbolTable.toFramed (table : GobjSymbolTable)
    (lengthFits : (writeGobjSymbolTable table).length < 2 ^ 32) :
    U32LengthPrefixedBytes :=
  ⟨writeGobjSymbolTable table, lengthFits⟩

/-- Parse an exact framed symbol-table body and reject trailing corruption. -/
def parseGobjSymbolTableBody (body : U32LengthPrefixedBytes) :
    Except ParseError GobjSymbolTable :=
  match readGobjSymbolTable body.bytes with
  | .done table rest =>
    if rest = Vec.empty then .ok table else .error .trailingInput
  | .needMore _ => .error (.malformed "truncated .gobj symbol-table body")
  | .invalid error => .error error

/-- `parseGobjSymbolTableBody_toFramed` recovers the exact canonical table. -/
@[simp] theorem parseGobjSymbolTableBody_toFramed (table : GobjSymbolTable)
    (lengthFits : (writeGobjSymbolTable table).length < 2 ^ 32) :
    parseGobjSymbolTableBody (table.toFramed lengthFits) = .ok table := by
  unfold parseGobjSymbolTableBody GobjSymbolTable.toFramed
  rw [readGobjSymbolTable_write]
  rfl

/-- Decode the typed symbol table retained in a raw payload envelope. -/
def GobjPayload.parseSymbols (payload : GobjPayload) :
    Except ParseError GobjSymbolTable :=
  parseGobjSymbolTableBody payload.symbols

/-- Replace only an envelope's symbol body with one canonical typed table. -/
def GobjPayload.withSymbolTable (payload : GobjPayload)
    (table : GobjSymbolTable)
    (lengthFits : (writeGobjSymbolTable table).length < 2 ^ 32) : GobjPayload :=
  { payload with symbols := table.toFramed lengthFits }

/-- `GobjPayload.parseSymbols_withSymbolTable` proves typed envelope recovery. -/
@[simp] theorem GobjPayload.parseSymbols_withSymbolTable
    (payload : GobjPayload) (table : GobjSymbolTable)
    (lengthFits : (writeGobjSymbolTable table).length < 2 ^ 32) :
    (payload.withSymbolTable table lengthFits).parseSymbols = .ok table := by
  exact parseGobjSymbolTableBody_toFramed table lengthFits

end Grass.Artifact.Binary.Gobj
