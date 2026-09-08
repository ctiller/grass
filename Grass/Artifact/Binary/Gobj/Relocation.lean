import Grass.Artifact.Binary.Gobj.Symbol

/-!
# Typed `.gobj` relocation entries

`GobjRelocation` realizes the target-independent relocation container. Its
`kind` is an opaque tag whose machine-specific meaning remains owned by the
target ISA layer. This module owns only the generic algebra that consumes a
target-supplied positive patch width.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- One target-independent symbolic relocation record. -/
structure GobjRelocation where
  sectionIndex : BitVec 32
  offset : BitVec 64
  targetSymbolIndex : BitVec 32
  kind : BitVec 32
  addend : BitVec 64
deriving DecidableEq, Repr

/-- Reference validity against decoded section and symbol table sizes.

This predicate is deliberately only a syntactic/container check. It is not the
complete resolved-relocation boundary; use `GobjRelocation.ValidFor` for that. -/
def GobjRelocation.IndicesValid (entry : GobjRelocation)
    (sectionCount symbolCount : Nat) : Prop :=
  entry.sectionIndex.toNat < sectionCount ∧
    entry.targetSymbolIndex.toNat < symbolCount

instance (entry : GobjRelocation) (sectionCount symbolCount : Nat) :
    Decidable (entry.IndicesValid sectionCount symbolCount) := by
  unfold GobjRelocation.IndicesValid
  infer_instance

/-- Target-owned interpretation of opaque relocation kinds.

The target ISA layer supplies the facts; the artifact layer consumes only a
positive byte width. Returning `none` rejects an unknown kind. -/
structure RelocationKindInterpretation where
  profile : GobjRelocationProfileId
  patchWidth : BitVec 32 → Option Nat
  patchWidth_positive : ∀ {kind width}, patchWidth kind = some width → 0 < width

/-- An interpretation assigning the same positive width to every kind. -/
def RelocationKindInterpretation.constant (profile : GobjRelocationProfileId)
    (width : Nat) (positive : 0 < width) :
    RelocationKindInterpretation where
  profile := profile
  patchWidth _ := some width
  patchWidth_positive := by
    intro kind observed h
    simp only [Option.some.injEq] at h
    subst observed
    exact positive

/-- An interpretation recognizing exactly one numeric kind. -/
def RelocationKindInterpretation.singleKind
    (profile : GobjRelocationProfileId) (knownKind : BitVec 32)
    (width : Nat) (positive : 0 < width) : RelocationKindInterpretation where
  profile := profile
  patchWidth kind := if kind = knownKind then some width else none
  patchWidth_positive := by
    intro kind observed h
    split at h
    next =>
      simp only [Option.some.injEq] at h
      subst observed
      exact positive
    next => contradiction

/-- Target-owned registry selected by a serialized nominal profile identity. -/
structure RelocationProfileRegistry where
  resolve : GobjRelocationProfileId → Option RelocationKindInterpretation

/-- Executable complete check of a resolved relocation. -/
def GobjRelocation.isValidFor (entry : GobjRelocation)
    (registry : RelocationProfileRegistry)
    (sections : GobjSectionTable) (symbols : GobjSymbolTable) : Bool :=
  decide (entry.IndicesValid sections.entries.length symbols.entries.length) &&
    match sections.entries.get? entry.sectionIndex.toNat with
    | none => false
    | some target =>
      match target.profile with
      | .noRelocations => false
      | .relocatable profile =>
        match registry.resolve profile with
        | none => false
        | some interpretation =>
          decide (interpretation.profile = profile) &&
            match interpretation.patchWidth entry.kind with
            | none => false
            | some width =>
              decide (entry.offset.toNat < target.contents.bytes.length) &&
                decide (entry.offset.toNat + width ≤ target.contents.bytes.length)

/-- Complete generic validity of a resolved relocation.

The selected section and symbol must exist, the target must recognize the kind,
and the positive-width patch must fit entirely in the selected section. The
addition is performed in `Nat`, so it cannot wrap like fixed-width arithmetic. -/
def GobjRelocation.ValidFor (entry : GobjRelocation)
    (registry : RelocationProfileRegistry)
    (sections : GobjSectionTable) (symbols : GobjSymbolTable) : Prop :=
  entry.isValidFor registry sections symbols = true

instance (entry : GobjRelocation)
    (registry : RelocationProfileRegistry)
    (sections : GobjSectionTable) (symbols : GobjSymbolTable) :
    Decidable (entry.ValidFor registry sections symbols) := by
  unfold GobjRelocation.ValidFor
  infer_instance

/-- Serialize one fixed-width target-independent relocation entry. -/
def writeGobjRelocation (entry : GobjRelocation) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) entry.sectionIndex ++
  writeLittleEndian (count := 8) entry.offset ++
  writeLittleEndian (count := 4) entry.targetSymbolIndex ++
  writeLittleEndian (count := 4) entry.kind ++
  writeLittleEndian (count := 8) entry.addend

/-- Parse one fixed-width relocation while retaining the exact suffix. -/
def readGobjRelocation (input : Std.Logical.ByteArray) :
    ParseResult GobjRelocation :=
  match takeLittleEndian 4 input with
  | .done sectionIndex afterSectionIndex =>
    match takeLittleEndian 8 afterSectionIndex with
    | .done offset afterOffset =>
      match takeLittleEndian 4 afterOffset with
      | .done targetSymbolIndex afterTarget =>
        match takeLittleEndian 4 afterTarget with
        | .done kind afterKind =>
          match takeLittleEndian 8 afterKind with
          | .done addend suffix =>
            .done { sectionIndex, offset, targetSymbolIndex, kind, addend } suffix
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

/-- `length_writeGobjRelocation` fixes every relocation entry at 28 bytes. -/
@[simp] theorem length_writeGobjRelocation (entry : GobjRelocation) :
    (writeGobjRelocation entry).length = 28 := by
  simp [writeGobjRelocation]

/-- `readGobjRelocation_write_append` parses one canonical relocation and
preserves every following suffix. -/
@[simp] theorem readGobjRelocation_write_append (entry : GobjRelocation)
    (suffix : Std.Logical.ByteArray) :
    readGobjRelocation (writeGobjRelocation entry ++ suffix) =
      .done entry suffix := by
  unfold readGobjRelocation writeGobjRelocation
  simp only [Vec.append_assoc]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [takeLittleEndian_writeLittleEndian_append]

/-- `readGobjRelocation_write` is the complete-input relocation round trip. -/
@[simp] theorem readGobjRelocation_write (entry : GobjRelocation) :
    readGobjRelocation (writeGobjRelocation entry) =
      .done entry Vec.empty := by
  simpa using readGobjRelocation_write_append entry Vec.empty

/-- Serialize relocation entries consecutively in canonical source order. -/
def writeGobjRelocationList : List GobjRelocation → Std.Logical.ByteArray
  | [] => Vec.empty
  | entry :: entries =>
    writeGobjRelocation entry ++ writeGobjRelocationList entries

/-- The relocation-list writer emits exactly 28 bytes per entry. -/
@[simp] theorem length_writeGobjRelocationList
    (entries : List GobjRelocation) :
    (writeGobjRelocationList entries).length = 28 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp [writeGobjRelocationList, ih]
      omega

/-- Parse exactly `count` consecutive relocation entries. -/
def readGobjRelocationList : Nat → Std.Logical.ByteArray →
    ParseResult (List GobjRelocation)
  | 0, input => .done [] input
  | count + 1, input =>
    match readGobjRelocation input with
    | .done entry rest =>
      match readGobjRelocationList count rest with
      | .done entries suffix => .done (entry :: entries) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- `readGobjRelocationList_write_append` parses a canonical relocation list
exactly and preserves an arbitrary suffix. -/
@[simp] theorem readGobjRelocationList_write_append
    (entries : List GobjRelocation) (suffix : Std.Logical.ByteArray) :
    readGobjRelocationList entries.length
        (writeGobjRelocationList entries ++ suffix) =
      .done entries suffix := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.length_cons, writeGobjRelocationList, Vec.append_assoc,
        readGobjRelocationList]
      rw [readGobjRelocation_write_append]
      simp only
      rw [ih]

/-- A count-representable ordered table of relocations. -/
structure GobjRelocationTable where
  entries : Vec GobjRelocation
  countFits : entries.length < 2 ^ 32
deriving DecidableEq, Repr

/-- Every relocation in a table refers to an existing section and symbol. -/
def GobjRelocationTable.IndicesValid (table : GobjRelocationTable)
    (sections : GobjSectionTable) (symbols : GobjSymbolTable) : Prop :=
  ∀ entry ∈ table.entries.toList,
    entry.IndicesValid sections.entries.length symbols.entries.length

instance (table : GobjRelocationTable) (sections : GobjSectionTable)
    (symbols : GobjSymbolTable) :
    Decidable (table.IndicesValid sections symbols) :=
  by
    unfold GobjRelocationTable.IndicesValid
    infer_instance

/-- Every relocation in a table is completely valid under one target profile. -/
def GobjRelocationTable.ValidFor (table : GobjRelocationTable)
    (registry : RelocationProfileRegistry)
    (sections : GobjSectionTable) (symbols : GobjSymbolTable) : Prop :=
  ∀ entry ∈ table.entries.toList,
    entry.ValidFor registry sections symbols

instance (table : GobjRelocationTable)
    (registry : RelocationProfileRegistry)
    (sections : GobjSectionTable) (symbols : GobjSymbolTable) :
    Decidable (table.ValidFor registry sections symbols) := by
    unfold GobjRelocationTable.ValidFor
    infer_instance

/-- A relocation table admitted across the target-aware resolved boundary. -/
structure ResolvedGobjRelocationTable
    (registry : RelocationProfileRegistry)
    (sections : GobjSectionTable) (symbols : GobjSymbolTable) where
  table : GobjRelocationTable
  valid : table.ValidFor registry sections symbols

/-- Check all target-aware patch bounds and retain their proof on success. -/
def resolveGobjRelocationTable
    (registry : RelocationProfileRegistry)
    (sections : GobjSectionTable) (symbols : GobjSymbolTable)
    (table : GobjRelocationTable) :
    Except ParseError
      (ResolvedGobjRelocationTable registry sections symbols) :=
  if valid : table.ValidFor registry sections symbols then
    .ok { table := table, valid := valid }
  else
    .error (.malformed ".gobj relocation patch is out of bounds or unknown")

/-- Serialize a relocation count and all fixed-width entries. -/
def writeGobjRelocationTable (table : GobjRelocationTable) :
    Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (BitVec.ofNat 32 table.entries.length) ++
    writeGobjRelocationList table.entries.toList

/-- Parse a relocation table after checking its exact fixed-width extent. -/
def readGobjRelocationTable (input : Std.Logical.ByteArray) :
    ParseResult GobjRelocationTable :=
  match takeLittleEndian 4 input with
  | .done count rest =>
    if _minimumFits : 28 * count.toNat ≤ rest.length then
      match readGobjRelocationList count.toNat rest with
      | .done entries suffix =>
        if countExact : entries.length = count.toNat then
          .done {
            entries := Vec.fromList entries
            countFits := by
              simp only [Vec.length_fromList, countExact]
              simpa using BitVec.isLt count } suffix
        else
          .invalid (.malformed ".gobj relocation-count mismatch")
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else
      .needMore (some (28 * count.toNat - rest.length))
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- `length_writeGobjRelocationTable` gives the table's exact encoded width. -/
@[simp] theorem length_writeGobjRelocationTable (table : GobjRelocationTable) :
    (writeGobjRelocationTable table).length =
      4 + 28 * table.entries.length := by
  simp [writeGobjRelocationTable]
  rfl

/-- `readGobjRelocationTable_write_append` parses a canonical relocation table
exactly and preserves every following suffix. -/
@[simp] theorem readGobjRelocationTable_write_append
    (table : GobjRelocationTable) (suffix : Std.Logical.ByteArray) :
    readGobjRelocationTable (writeGobjRelocationTable table ++ suffix) =
      .done table suffix := by
  have countEq : (BitVec.ofNat 32 table.entries.length).toNat =
      table.entries.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt table.countFits]
  have minimumFits :
      28 * (BitVec.ofNat 32 table.entries.length).toNat ≤
        (writeGobjRelocationList table.entries.toList ++ suffix).length := by
    rw [countEq, Vec.length_append, length_writeGobjRelocationList]
    change 28 * table.entries.toList.length ≤
      28 * table.entries.toList.length + suffix.length
    exact Nat.le_add_right _ _
  have parsedEntries :
      readGobjRelocationList (BitVec.ofNat 32 table.entries.length).toNat
          (writeGobjRelocationList table.entries.toList ++ suffix) =
        .done table.entries.toList suffix := by
    rw [countEq]
    exact readGobjRelocationList_write_append table.entries.toList suffix
  have countExact : table.entries.toList.length =
      (BitVec.ofNat 32 table.entries.length).toNat := by
    rw [countEq]
    rfl
  unfold readGobjRelocationTable writeGobjRelocationTable
  rw [Vec.append_assoc, takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [dif_pos minimumFits]
  rw [parsedEntries]
  simp only
  rw [dif_pos countExact]

/-- The whole relocation-table round trip is the empty-suffix specialization. -/
@[simp] theorem readGobjRelocationTable_write (table : GobjRelocationTable) :
    readGobjRelocationTable (writeGobjRelocationTable table) =
      .done table Vec.empty := by
  simpa using readGobjRelocationTable_write_append table Vec.empty

/-- Embed a typed relocation table into the envelope's checked byte framing. -/
def GobjRelocationTable.toFramed (table : GobjRelocationTable)
    (lengthFits : (writeGobjRelocationTable table).length < 2 ^ 32) :
    U32LengthPrefixedBytes :=
  ⟨writeGobjRelocationTable table, lengthFits⟩

/-- Parse an exact framed relocation body and reject trailing corruption. -/
def parseGobjRelocationTableBody (body : U32LengthPrefixedBytes) :
    Except ParseError GobjRelocationTable :=
  match readGobjRelocationTable body.bytes with
  | .done table rest =>
    if rest = Vec.empty then .ok table else .error .trailingInput
  | .needMore _ => .error (.malformed "truncated .gobj relocation-table body")
  | .invalid error => .error error

/-- `parseGobjRelocationTableBody_toFramed` recovers the canonical table. -/
@[simp] theorem parseGobjRelocationTableBody_toFramed
    (table : GobjRelocationTable)
    (lengthFits : (writeGobjRelocationTable table).length < 2 ^ 32) :
    parseGobjRelocationTableBody (table.toFramed lengthFits) = .ok table := by
  unfold parseGobjRelocationTableBody GobjRelocationTable.toFramed
  rw [readGobjRelocationTable_write]
  rfl

/-- Decode the typed relocation table retained in a raw payload envelope. -/
def GobjPayload.parseRelocations (payload : GobjPayload) :
    Except ParseError GobjRelocationTable :=
  parseGobjRelocationTableBody payload.relocations

/-- Replace only an envelope's relocation body with one canonical table. -/
def GobjPayload.withRelocationTable (payload : GobjPayload)
    (table : GobjRelocationTable)
    (lengthFits : (writeGobjRelocationTable table).length < 2 ^ 32) :
    GobjPayload :=
  { payload with relocations := table.toFramed lengthFits }

/-- `GobjPayload.parseRelocations_withRelocationTable` proves envelope recovery. -/
@[simp] theorem GobjPayload.parseRelocations_withRelocationTable
    (payload : GobjPayload) (table : GobjRelocationTable)
    (lengthFits : (writeGobjRelocationTable table).length < 2 ^ 32) :
    (payload.withRelocationTable table lengthFits).parseRelocations =
      .ok table := by
  exact parseGobjRelocationTableBody_toFramed table lengthFits

end Grass.Artifact.Binary.Gobj
