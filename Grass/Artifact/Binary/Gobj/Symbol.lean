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

/-- A named, section-relative symbol with an overflow-safe half-open extent. -/
structure GobjSymbol where
  name : U32LengthPrefixedBytes
  binding : GobjSymbolBinding
  sectionIndex : BitVec 32
  offset : BitVec 64
  size : BitVec 64
  extentFits : offset.toNat + size.toNat ≤ 2 ^ 64
deriving DecidableEq, Repr

/-- Serialize one canonical symbol entry. -/
def writeGobjSymbol (entry : GobjSymbol) : Std.Logical.ByteArray :=
  writeU32LengthPrefixedBytes entry.name ++
  writeByte entry.binding.toByte ++
  writeLittleEndian (count := 3) (0 : BitVec 24) ++
  writeLittleEndian (count := 4) entry.sectionIndex ++
  writeLittleEndian (count := 8) entry.offset ++
  writeLittleEndian (count := 8) entry.size

/-- Parse one symbol entry while retaining the exact unconsumed suffix. -/
def readGobjSymbol (input : Std.Logical.ByteArray) : ParseResult GobjSymbol :=
  match readU32LengthPrefixedBytes input with
  | .done name afterName =>
    match takeByte afterName with
    | .done bindingBits afterBinding =>
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
                    .done {
                      name := name
                      binding := binding
                      sectionIndex := sectionIndex
                      offset := offset
                      size := size
                      extentFits := extentFits } suffix
                  else
                    .invalid (.malformed ".gobj symbol extent overflows 64 bits")
                | .needMore hint => .needMore hint
                | .invalid error => .invalid error
              | .needMore hint => .needMore hint
              | .invalid error => .invalid error
            | .needMore hint => .needMore hint
            | .invalid error => .invalid error
          else
            .invalid (.malformed "nonzero .gobj symbol reserved field")
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .error error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- `length_writeGobjSymbol` gives the exact symbol-entry width. -/
@[simp] theorem length_writeGobjSymbol (entry : GobjSymbol) :
    (writeGobjSymbol entry).length = 28 + entry.name.bytes.length := by
  simp [writeGobjSymbol, writeByte]
  omega

/-- `readGobjSymbol_write_append` parses one canonical symbol exactly and
preserves every following suffix. -/
@[simp] theorem readGobjSymbol_write_append (entry : GobjSymbol)
    (suffix : Std.Logical.ByteArray) :
    readGobjSymbol (writeGobjSymbol entry ++ suffix) = .done entry suffix := by
  unfold readGobjSymbol writeGobjSymbol
  simp only [Vec.append_assoc]
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [takeByte_writeByte_append]
  simp only [readGobjSymbolBinding_toByte]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only [dite_true]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [dif_pos entry.extentFits]

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
    28 + entry.name.bytes.length + gobjSymbolListLength entries

/-- The recursive symbol-list writer has its exact declared width. -/
@[simp] theorem length_writeGobjSymbolList (entries : List GobjSymbol) :
    (writeGobjSymbolList entries).length = gobjSymbolListLength entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp [writeGobjSymbolList, gobjSymbolListLength, ih]

/-- `minLength_gobjSymbolList` bounds each encoded symbol by 28 bytes. -/
theorem minLength_gobjSymbolList (entries : List GobjSymbol) :
    28 * entries.length ≤ gobjSymbolListLength entries := by
  induction entries with
  | nil => simp [gobjSymbolListLength]
  | cons entry entries ih =>
      simp only [List.length_cons, gobjSymbolListLength]
      omega

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
    | .needMore hint => .needMore hint
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
  namesUnique : (entries.toList.map fun entry => entry.name.bytes).Nodup
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
    if _minimumFits : 28 * count.toNat ≤ rest.length then
      match readGobjSymbolList count.toNat rest with
      | .done entries suffix =>
        if countExact : entries.length = count.toNat then
          if namesUnique : (entries.map fun entry => entry.name.bytes).Nodup then
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
    else
      .needMore (some (28 * count.toNat - rest.length))
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
  have minimumFits :
      28 * (BitVec.ofNat 32 table.entries.length).toNat ≤
        (writeGobjSymbolList table.entries.toList ++ suffix).length := by
    rw [countEq, Vec.length_append, length_writeGobjSymbolList]
    change 28 * table.entries.toList.length ≤
      gobjSymbolListLength table.entries.toList + suffix.length
    exact Nat.le_trans (minLength_gobjSymbolList table.entries.toList)
      (Nat.le_add_right _ _)
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
  rw [dif_pos minimumFits]
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
