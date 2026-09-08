import Grass.Artifact.Binary.Gobj.Payload

/-!
# Typed `.gobj` section entries

`GobjSection` records a proof-free relocatable section name, checked power-of-two
alignment exponent, reserved-free permission bits, and uninterpreted contents.
Machine-specific relocation meaning remains outside this container layer.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- A base-two section-alignment exponent bounded to the 32-bit object domain. -/
structure GobjSectionAlignment where
  bits : Byte
  valid : bits.toNat ≤ 31
deriving DecidableEq, Repr

/-- Section permission bits restricted to readable, writable, and executable. -/
structure GobjSectionPermissions where
  bits : Byte
  reservedClear : bits.toNat < 8
deriving DecidableEq, Repr

/-- Structured nominal identity for a target-owned relocation interpretation. -/
structure GobjRelocationProfileId where
  owner : U32LengthPrefixedBytes
  name : U32LengthPrefixedBytes
  version : BitVec 32
deriving DecidableEq, Repr

/-- A section either forbids relocations or names their exact interpretation. -/
inductive GobjSectionProfile where
  | noRelocations
  | relocatable (id : GobjRelocationProfileId)
deriving DecidableEq, Repr

/-- Canonical serialization of a structured section profile. -/
def writeGobjSectionProfile : GobjSectionProfile → Std.Logical.ByteArray
  | .noRelocations => writeByte 0
  | .relocatable id =>
    writeByte 1 ++ writeU32LengthPrefixedBytes id.owner ++
      writeU32LengthPrefixedBytes id.name ++
      writeLittleEndian (count := 4) id.version

/-- Decode a structured section profile and reject unknown profile tags. -/
def readGobjSectionProfile (input : Std.Logical.ByteArray) :
    ParseResult GobjSectionProfile :=
  match takeByte input with
  | .done tag rest =>
    if tag = 0 then .done .noRelocations rest
    else if tag = 1 then
      match readU32LengthPrefixedBytes rest with
      | .done owner afterOwner =>
        match readU32LengthPrefixedBytes afterOwner with
        | .done name afterName =>
          match takeLittleEndian 4 afterName with
          | .done version suffix =>
            .done (.relocatable { owner, name, version }) suffix
          | .needMore hint => .needMore hint
          | .invalid error => .invalid error
        | .needMore hint => requireAfter 4 (.needMore hint)
        | .invalid error => .invalid error
      | .needMore hint => requireAfter 8 (.needMore hint)
      | .invalid error => .invalid error
    else .invalid (.malformed "unknown .gobj section profile tag")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Exact encoded byte width of a section profile. -/
def gobjSectionProfileLength : GobjSectionProfile → Nat
  | .noRelocations => 1
  | .relocatable id => 13 + id.owner.bytes.length + id.name.bytes.length

@[simp] theorem length_writeGobjSectionProfile (profile : GobjSectionProfile) :
    (writeGobjSectionProfile profile).length = gobjSectionProfileLength profile := by
  cases profile with
  | noRelocations => simp [writeGobjSectionProfile, gobjSectionProfileLength, writeByte]
  | relocatable id =>
      simp [writeGobjSectionProfile, gobjSectionProfileLength, writeByte]
      omega

@[simp] theorem readGobjSectionProfile_write_append
    (profile : GobjSectionProfile) (suffix : Std.Logical.ByteArray) :
    readGobjSectionProfile (writeGobjSectionProfile profile ++ suffix) =
      .done profile suffix := by
  cases profile with
  | noRelocations =>
      unfold readGobjSectionProfile writeGobjSectionProfile
      rw [takeByte_writeByte_append]
      rfl
  | relocatable id =>
      unfold readGobjSectionProfile writeGobjSectionProfile
      simp only [Vec.append_assoc]
      rw [takeByte_writeByte_append]
      simp only
      rw [if_neg (by decide : (1 : Byte) ≠ 0)]
      rw [if_pos True.intro]
      rw [readU32LengthPrefixedBytes_write_append]
      simp only
      rw [readU32LengthPrefixedBytes_write_append]
      simp only
      rw [takeLittleEndian_writeLittleEndian_append]

theorem one_le_gobjSectionProfileLength (profile : GobjSectionProfile) :
    1 ≤ gobjSectionProfileLength profile := by
  cases profile <;> simp [gobjSectionProfileLength] <;> omega

/-- One proof-free relocatable section entry. -/
structure GobjSection where
  name : U32LengthPrefixedBytes
  alignment : GobjSectionAlignment
  permissions : GobjSectionPermissions
  profile : GobjSectionProfile := .noRelocations
  contents : U32LengthPrefixedBytes
deriving DecidableEq, Repr

/-- Decode and validate a serialized alignment exponent. -/
def readGobjSectionAlignment (bits : Byte) :
    Except ParseError GobjSectionAlignment :=
  if valid : bits.toNat ≤ 31 then .ok ⟨bits, valid⟩
  else .error (.malformed ".gobj section alignment exponent exceeds 31")

/-- A valid alignment exponent round-trips through its decoder. -/
@[simp] theorem readGobjSectionAlignment_bits
    (alignment : GobjSectionAlignment) :
    readGobjSectionAlignment alignment.bits = .ok alignment := by
  unfold readGobjSectionAlignment
  rw [dif_pos alignment.valid]

/-- Decode and reject any reserved section-permission bit. -/
def readGobjSectionPermissions (bits : Byte) :
    Except ParseError GobjSectionPermissions :=
  if reservedClear : bits.toNat < 8 then .ok ⟨bits, reservedClear⟩
  else .error (.malformed ".gobj section permission reserved bit is set")

/-- Valid permission bits round-trip through their decoder. -/
@[simp] theorem readGobjSectionPermissions_bits
    (permissions : GobjSectionPermissions) :
    readGobjSectionPermissions permissions.bits = .ok permissions := by
  unfold readGobjSectionPermissions
  rw [dif_pos permissions.reservedClear]

/-- Serialize one canonical section entry. -/
def writeGobjSection (entry : GobjSection) : Std.Logical.ByteArray :=
  writeU32LengthPrefixedBytes entry.name ++
  writeByte entry.alignment.bits ++
  writeByte entry.permissions.bits ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeGobjSectionProfile entry.profile ++
  writeU32LengthPrefixedBytes entry.contents

/-- Parse one section entry, validating alignment, permissions, and reserved
bytes while retaining the exact suffix. -/
def readGobjSection (input : Std.Logical.ByteArray) : ParseResult GobjSection :=
  match readU32LengthPrefixedBytes input with
  | .done name afterName =>
    match takeByte afterName with
    | .done alignmentBits afterAlignment =>
      match readGobjSectionAlignment alignmentBits with
      | .ok alignment =>
        match takeByte afterAlignment with
        | .done permissionBits afterPermissions =>
          match readGobjSectionPermissions permissionBits with
          | .ok permissions =>
            match takeLittleEndian 2 afterPermissions with
            | .done reserved afterReserved =>
              if _reservedOk : reserved = 0 then
                match readGobjSectionProfile afterReserved with
                | .done profile afterProfile =>
                  match readU32LengthPrefixedBytes afterProfile with
                  | .done contents suffix =>
                    .done { name, alignment, permissions, profile, contents } suffix
                  | .needMore hint => .needMore hint
                  | .invalid error => .invalid error
                | .needMore hint => requireAfter 4 (.needMore hint)
                | .invalid error => .invalid error
              else
                .invalid (.malformed
                  "nonzero .gobj section reserved field")
            | .needMore hint => requireAfter 5 (.needMore hint)
            | .invalid error => .invalid error
          | .error error => .invalid error
        | .needMore hint => requireAfter 7 (.needMore hint)
        | .invalid error => .invalid error
      | .error error => .invalid error
    | .needMore hint => requireAfter 8 (.needMore hint)
    | .invalid error => .invalid error
  | .needMore hint => requireAfter 9 (.needMore hint)
  | .invalid error => .invalid error

/-- `length_writeGobjSection` gives the exact section-entry width. -/
@[simp] theorem length_writeGobjSection (entry : GobjSection) :
    (writeGobjSection entry).length =
      12 + entry.name.bytes.length + gobjSectionProfileLength entry.profile +
        entry.contents.bytes.length := by
  simp [writeGobjSection, writeByte]
  omega

/-- `readGobjSection_write_append` parses one canonical section exactly and
preserves every following suffix. -/
@[simp] theorem readGobjSection_write_append (entry : GobjSection)
    (suffix : Std.Logical.ByteArray) :
    readGobjSection (writeGobjSection entry ++ suffix) =
      .done entry suffix := by
  unfold readGobjSection writeGobjSection
  simp only [Vec.append_assoc]
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [takeByte_writeByte_append]
  simp only [readGobjSectionAlignment_bits]
  rw [takeByte_writeByte_append]
  simp only [readGobjSectionPermissions_bits]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only [dite_true]
  rw [readGobjSectionProfile_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]

/-- `readGobjSection_write` is the complete-input section round trip. -/
@[simp] theorem readGobjSection_write (entry : GobjSection) :
    readGobjSection (writeGobjSection entry) = .done entry Vec.empty := by
  simpa using readGobjSection_write_append entry Vec.empty

/-- Serialize section entries consecutively in their canonical source order. -/
def writeGobjSectionList : List GobjSection → Std.Logical.ByteArray
  | [] => Vec.empty
  | entry :: entries => writeGobjSection entry ++ writeGobjSectionList entries

/-- Total canonical byte width of a section-entry list. -/
def gobjSectionListLength : List GobjSection → Nat
  | [] => 0
  | entry :: entries =>
    12 + entry.name.bytes.length + gobjSectionProfileLength entry.profile +
      entry.contents.bytes.length +
      gobjSectionListLength entries

/-- The recursive section-list writer has its exact declared width. -/
@[simp] theorem length_writeGobjSectionList (entries : List GobjSection) :
    (writeGobjSectionList entries).length = gobjSectionListLength entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp [writeGobjSectionList, gobjSectionListLength, ih]

/-- Every encoded section entry contributes at least its 13-byte framing. -/
theorem minLength_gobjSectionList (entries : List GobjSection) :
    13 * entries.length ≤ gobjSectionListLength entries := by
  induction entries with
  | nil => simp [gobjSectionListLength]
  | cons entry entries ih =>
      simp only [List.length_cons, gobjSectionListLength]
      have profileMinimum := one_le_gobjSectionProfileLength entry.profile
      omega

/-- Parse exactly `count` consecutive section entries. -/
def readGobjSectionList : Nat → Std.Logical.ByteArray →
    ParseResult (List GobjSection)
  | 0, input => .done [] input
  | count + 1, input =>
    match readGobjSection input with
    | .done entry rest =>
      match readGobjSectionList count rest with
      | .done entries suffix => .done (entry :: entries) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => requireAfter (13 * count) (.needMore hint)
    | .invalid error => .invalid error

/-- `readGobjSectionList_write_append` parses a canonical section list exactly
and preserves an arbitrary suffix. -/
@[simp] theorem readGobjSectionList_write_append (entries : List GobjSection)
    (suffix : Std.Logical.ByteArray) :
    readGobjSectionList entries.length (writeGobjSectionList entries ++ suffix) =
      .done entries suffix := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.length_cons, writeGobjSectionList, Vec.append_assoc,
        readGobjSectionList]
      rw [readGobjSection_write_append]
      simp only
      rw [ih]

/-- A count-representable ordered table of typed `.gobj` sections. -/
structure GobjSectionTable where
  entries : Vec GobjSection
  countFits : entries.length < 2 ^ 32
deriving DecidableEq, Repr

/-- Serialize a section count and all canonical entries. -/
def writeGobjSectionTable (table : GobjSectionTable) :
    Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (BitVec.ofNat 32 table.entries.length) ++
    writeGobjSectionList table.entries.toList

/-- Parse a section table entry by entry. Recursion advances only after an entry
has consumed at least thirteen bytes, so work is bounded by available input. -/
def readGobjSectionTable (input : Std.Logical.ByteArray) :
    ParseResult GobjSectionTable :=
  match takeLittleEndian 4 input with
  | .done count rest =>
    match readGobjSectionList count.toNat rest with
    | .done entries suffix =>
      if countExact : entries.length = count.toNat then
        .done {
          entries := Vec.fromList entries
          countFits := by
            simp only [Vec.length_fromList, countExact]
            simpa using BitVec.isLt count } suffix
      else
        .invalid (.malformed ".gobj section-count mismatch")
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- The complete table writer has four count bytes plus all entry bytes. -/
@[simp] theorem length_writeGobjSectionTable (table : GobjSectionTable) :
    (writeGobjSectionTable table).length =
      4 + gobjSectionListLength table.entries.toList := by
  simp [writeGobjSectionTable]

/-- `readGobjSectionTable_write_append` parses a canonical typed section table
exactly and preserves every following suffix. -/
@[simp] theorem readGobjSectionTable_write_append (table : GobjSectionTable)
    (suffix : Std.Logical.ByteArray) :
    readGobjSectionTable (writeGobjSectionTable table ++ suffix) =
      .done table suffix := by
  have countEq : (BitVec.ofNat 32 table.entries.length).toNat =
      table.entries.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt table.countFits]
  have parsedEntries :
      readGobjSectionList (BitVec.ofNat 32 table.entries.length).toNat
          (writeGobjSectionList table.entries.toList ++ suffix) =
        .done table.entries.toList suffix := by
    rw [countEq]
    exact readGobjSectionList_write_append table.entries.toList suffix
  have countExact : table.entries.toList.length =
      (BitVec.ofNat 32 table.entries.length).toNat := by
    rw [countEq]
    rfl
  unfold readGobjSectionTable writeGobjSectionTable
  rw [Vec.append_assoc, takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [parsedEntries]
  simp only
  rw [dif_pos countExact]

/-- The whole table round trip is the empty-suffix specialization. -/
@[simp] theorem readGobjSectionTable_write (table : GobjSectionTable) :
    readGobjSectionTable (writeGobjSectionTable table) =
      .done table Vec.empty := by
  simpa using readGobjSectionTable_write_append table Vec.empty

/-- Embed a typed section table into the envelope's checked byte framing. -/
def GobjSectionTable.toFramed (table : GobjSectionTable)
    (lengthFits : (writeGobjSectionTable table).length < 2 ^ 32) :
    U32LengthPrefixedBytes :=
  ⟨writeGobjSectionTable table, lengthFits⟩

/-- Parse an exact framed section-table body and reject trailing corruption. -/
def parseGobjSectionTableBody (body : U32LengthPrefixedBytes) :
    Except ParseError GobjSectionTable :=
  match readGobjSectionTable body.bytes with
  | .done table rest =>
    if rest = Vec.empty then .ok table else .error .trailingInput
  | .needMore _ =>
    .error (.malformed "truncated .gobj section-table body")
  | .invalid error => .error error

/-- A framed canonical section table parses back to the exact typed table. -/
@[simp] theorem parseGobjSectionTableBody_toFramed (table : GobjSectionTable)
    (lengthFits : (writeGobjSectionTable table).length < 2 ^ 32) :
    parseGobjSectionTableBody (table.toFramed lengthFits) = .ok table := by
  unfold parseGobjSectionTableBody GobjSectionTable.toFramed
  rw [readGobjSectionTable_write]
  rfl

/-- Decode the typed section table retained in a raw payload envelope. -/
def GobjPayload.parseSections (payload : GobjPayload) :
    Except ParseError GobjSectionTable :=
  parseGobjSectionTableBody payload.sections

/-- Replace only an envelope's section body with one canonical typed table. -/
def GobjPayload.withSectionTable (payload : GobjPayload)
    (table : GobjSectionTable)
    (lengthFits : (writeGobjSectionTable table).length < 2 ^ 32) : GobjPayload :=
  { payload with sections := table.toFramed lengthFits }

/-- Replacing an envelope section body makes `GobjPayload.parseSections`
recover that exact table. -/
@[simp] theorem GobjPayload.parseSections_withSectionTable
    (payload : GobjPayload) (table : GobjSectionTable)
    (lengthFits : (writeGobjSectionTable table).length < 2 ^ 32) :
    (payload.withSectionTable table lengthFits).parseSections = .ok table := by
  exact parseGobjSectionTableBody_toFramed table lengthFits

end Grass.Artifact.Binary.Gobj
