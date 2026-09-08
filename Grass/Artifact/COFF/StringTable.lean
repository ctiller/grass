import Grass.Artifact.COFF.SymbolName

/-!
# COFF string tables

A COFF string table begins with a little-endian 32-bit total size that includes
the size word itself. `StringTable` retains both the declared size and its exact
equation to the payload. Symbol-name offset validity is then checked against the
same parsed table rather than against an unrelated byte buffer.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- A syntactically valid COFF string table. The minimum excludes the malformed
declared sizes zero through three; `sizeMatches` prevents truncated or trailing
payload bytes from being absorbed into the value. -/
structure StringTable where
  declaredSize : BitVec 32
  payload : Std.Logical.ByteArray
  minimumSize : 4 ≤ declaredSize.toNat
  sizeMatches : declaredSize.toNat = payload.length + 4
deriving DecidableEq, Repr

/-- Proof-bearing grammar representation of a string table. -/
abbrev CheckedStringTable :=
  {table : BitVec 32 × Std.Logical.ByteArray //
    4 ≤ table.1.toNat ∧ table.1.toNat = table.2.length + 4}

/-- Restore named string-table fields from the checked grammar value. -/
def StringTable.ofChecked (table : CheckedStringTable) : StringTable where
  declaredSize := table.1.1
  payload := table.1.2
  minimumSize := table.2.1
  sizeMatches := table.2.2

/-- Forget only field labels while retaining both size proofs. -/
def StringTable.toChecked (table : StringTable) : CheckedStringTable :=
  ⟨(table.declaredSize, table.payload), table.minimumSize, table.sizeMatches⟩

/-- Named and checked string-table representations are totally isomorphic. -/
def stringTableIsomorphism : Isomorphism CheckedStringTable StringTable where
  forward := StringTable.ofChecked
  backward := StringTable.toChecked
  backward_forward := by
    intro table
    rcases table with ⟨⟨declared, payload⟩, minimum, size⟩
    rfl
  forward_backward := by
    intro table
    rcases table with ⟨declared, payload, minimum, size⟩
    rfl

/-- Raw length-directed string-table grammar before validity refinement. -/
def rawStringTableFormat :
    Format (BitVec 32 × Std.Logical.ByteArray) :=
  .seq littleEndianU32Format fun declared =>
    repeatedBytesFormat (declared.toNat - 4)

/-- Refine raw size-directed bytes by the four-byte minimum and exact equation. -/
def checkedStringTableFormat : Format CheckedStringTable :=
  rawStringTableFormat.refineValue fun table =>
    4 ≤ table.1.toNat ∧ table.1.toNat = table.2.length + 4

/-- Typed language of a syntactically valid COFF string table. -/
def stringTableFormat : Format StringTable :=
  checkedStringTableFormat.iso stringTableIsomorphism

/-- Parse one size-prefixed COFF string table, retaining following bytes as the
exact suffix. Declared sizes below four are irrecoverably malformed. -/
def readStringTable (input : Std.Logical.ByteArray) : ParseResult StringTable :=
  match takeLittleEndian 4 input with
  | .done declaredSize rest =>
    if minimum : 4 ≤ declaredSize.toNat then
      let payloadSize := declaredSize.toNat - 4
      match takeExactSized payloadSize rest with
      | .done payload suffix => .done {
          declaredSize
          payload := payload.1
          minimumSize := minimum
          sizeMatches := by rw [payload.2]; omega } suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else
      .invalid (.malformed "COFF string-table size is below four")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Serialize the retained size word and its exactly coupled payload. -/
def writeStringTable (table : StringTable) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) table.declaredSize ++ table.payload

/-- Serialized string-table length equals its retained declared size. -/
@[simp] theorem length_writeStringTable (table : StringTable) :
    (writeStringTable table).length = table.declaredSize.toNat := by
  simp [writeStringTable, writeLittleEndian, isoWriter, writeExact,
    table.sizeMatches, Nat.add_comm]

/-- Every serialized valid string table derives from its size-refined grammar. -/
theorem writeStringTable_derives (table : StringTable) :
    Derives stringTableFormat (writeStringTable table) table Vec.empty := by
  rcases table with ⟨declared, payload, minimum, size⟩
  unfold stringTableFormat
  refine @Derives.iso CheckedStringTable StringTable checkedStringTableFormat
    stringTableIsomorphism _ Vec.empty
    ⟨(declared, payload), minimum, size⟩ ?_
  unfold checkedStringTableFormat
  apply Derives.lift
  unfold rawStringTableFormat writeStringTable
  have payloadLength : payload.length = declared.toNat - 4 := by omega
  exact Derives.seqAppend
    ((writeLittleEndian_realizes 4).sound declared)
    (by simpa [payloadLength] using anyBytes_derives payload Vec.empty)

/-- Valid string tables round-trip while preserving an arbitrary suffix. -/
@[simp] theorem readStringTable_writeStringTable_append
    (table : StringTable) (rest : Std.Logical.ByteArray) :
    readStringTable (writeStringTable table ++ rest) = .done table rest := by
  rcases table with ⟨declared, payload, minimum, size⟩
  simp only [readStringTable, writeStringTable, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]
  simp only [minimum, dite_true]
  have payloadLength : payload.length = declared.toNat - 4 := by omega
  have parsed := takeExactSized_writeExact_append
    (value := ⟨payload, payloadLength⟩) rest
  simp only [writeExact] at parsed
  rw [parsed]

/-- Whole-table canonical writer/reader round trip. -/
@[simp] theorem readStringTable_writeStringTable (table : StringTable) :
    readStringTable (writeStringTable table) = .done table Vec.empty := by
  simpa using readStringTable_writeStringTable_append table Vec.empty

/-- Whether an offset points into the payload and has a terminating NUL at or
after that position. The offset is measured from the start of the size word. -/
def StringTable.ValidOffset (table : StringTable) (offset : BitVec 32) : Prop :=
  4 ≤ offset.toNat ∧
  offset.toNat < table.declaredSize.toNat ∧
  (table.payload.drop (offset.toNat - 4)).contains 0 = true

instance (table : StringTable) (offset : BitVec 32) :
    Decidable (table.ValidOffset offset) := by
  unfold StringTable.ValidOffset
  infer_instance

/-- Contextual validity of typed symbol-name syntax in one parsed string table.
Inline names need no table lookup; long names use `StringTable.ValidOffset`. -/
def SymbolName.ValidIn (name : SymbolName) (table : StringTable) : Prop :=
  match name with
  | .inline _ _ _ => True
  | .stringTableOffset offset => table.ValidOffset offset

instance (name : SymbolName) (table : StringTable) :
    Decidable (name.ValidIn table) := by
  cases name with
  | inline => exact isTrue trivial
  | stringTableOffset offset =>
      unfold SymbolName.ValidIn
      infer_instance

end Grass.Artifact.COFF
