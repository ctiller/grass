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

/-- One proof-free relocatable section entry. -/
structure GobjSection where
  name : U32LengthPrefixedBytes
  alignment : GobjSectionAlignment
  permissions : GobjSectionPermissions
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

/-- Successful alignment decoding returns exactly the structure carrying the
input byte. -/
theorem readGobjSectionAlignment_ok_iff (bits : Byte)
    (alignment : GobjSectionAlignment) :
    readGobjSectionAlignment bits = .ok alignment ↔
      bits = alignment.bits := by
  constructor
  · intro decoded
    unfold readGobjSectionAlignment at decoded
    split at decoded
    next valid =>
      injection decoded with equality
      exact congrArg GobjSectionAlignment.bits equality
    next => contradiction
  · intro equality
    subst bits
    exact readGobjSectionAlignment_bits alignment

/-- Independent byte language for a valid section-alignment exponent. -/
def gobjSectionAlignmentFormat : Format GobjSectionAlignment :=
  .lift (.refine anyByteFormat fun bits => bits.toNat ≤ 31)
    GobjSectionAlignment.bits

/-- The alignment format consumes exactly the canonical validated byte. -/
theorem derives_gobjSectionAlignment_iff
    {input rest : Std.Logical.ByteArray} {alignment : GobjSectionAlignment} :
    Derives gobjSectionAlignmentFormat input alignment rest ↔
      input = writeByte alignment.bits ++ rest := by
  constructor
  · intro derivation
    exact derivation.lift_inner.refine_inner.byteInput
  · intro equality
    rw [equality]
    apply Derives.lift
    apply Derives.refine
    · exact writeByte_realizes.derivesWithSuffix alignment.bits rest
    · exact alignment.valid

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

/-- Successful permission decoding returns exactly the structure carrying the
input byte. -/
theorem readGobjSectionPermissions_ok_iff (bits : Byte)
    (permissions : GobjSectionPermissions) :
    readGobjSectionPermissions bits = .ok permissions ↔
      bits = permissions.bits := by
  constructor
  · intro decoded
    unfold readGobjSectionPermissions at decoded
    split at decoded
    next reservedClear =>
      injection decoded with equality
      exact congrArg GobjSectionPermissions.bits equality
    next => contradiction
  · intro equality
    subst bits
    exact readGobjSectionPermissions_bits permissions

/-- Independent byte language for valid, reserved-free section permissions. -/
def gobjSectionPermissionsFormat : Format GobjSectionPermissions :=
  .lift (.refine anyByteFormat fun bits => bits.toNat < 8)
    GobjSectionPermissions.bits

/-- The permission format consumes exactly the canonical validated byte. -/
theorem derives_gobjSectionPermissions_iff
    {input rest : Std.Logical.ByteArray} {permissions : GobjSectionPermissions} :
    Derives gobjSectionPermissionsFormat input permissions rest ↔
      input = writeByte permissions.bits ++ rest := by
  constructor
  · intro derivation
    exact derivation.lift_inner.refine_inner.byteInput
  · intro equality
    rw [equality]
    apply Derives.lift
    apply Derives.refine
    · exact writeByte_realizes.derivesWithSuffix permissions.bits rest
    · exact permissions.reservedClear

/-- Nested representation used by the independent section-entry language. -/
abbrev GobjSectionFields :=
  U32LengthPrefixedBytes ×
    (GobjSectionAlignment ×
      (GobjSectionPermissions × (Unit × U32LengthPrefixedBytes)))

/-- Independent language for every field and invariant of one section entry. -/
def gobjSectionFieldsFormat : Format GobjSectionFields :=
  .seq u32LengthPrefixedBytesFormat fun _ =>
  .seq gobjSectionAlignmentFormat fun _ =>
  .seq gobjSectionPermissionsFormat fun _ =>
  .seq gobjReservedFormat fun _ =>
    u32LengthPrefixedBytesFormat

/-- Canonical writer over the nested section-entry representation. -/
def writeGobjSectionFields (fields : GobjSectionFields) :
    Std.Logical.ByteArray :=
  writeU32LengthPrefixedBytes fields.1 ++
  writeByte fields.2.1.bits ++
  writeByte fields.2.2.1.bits ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeU32LengthPrefixedBytes fields.2.2.2.2

/-- The independent nested section format denotes exactly its canonical
writer prefix. -/
theorem derives_gobjSectionFields_iff
    {input rest : Std.Logical.ByteArray} {fields : GobjSectionFields} :
    Derives gobjSectionFieldsFormat input fields rest ↔
      input = writeGobjSectionFields fields ++ rest := by
  unfold gobjSectionFieldsFormat writeGobjSectionFields
  rw [derives_canonicalSeq_iff derives_u32LengthPrefixedBytes_iff
    (derives_canonicalSeq_iff derives_gobjSectionAlignment_iff
      (derives_canonicalSeq_iff derives_gobjSectionPermissions_iff
        (derives_canonicalSeq_iff derives_gobjReserved_iff
          derives_u32LengthPrefixedBytes_iff)))]
  simp [Vec.append_assoc]

/-- Forget a public section entry into the values of the independent field
language. -/
def GobjSection.toFields (entry : GobjSection) : GobjSectionFields :=
  (entry.name, (entry.alignment, (entry.permissions, ((), entry.contents))))

/-- Independent typed language of canonical `.gobj` section entries. -/
def gobjSectionFormat : Format GobjSection :=
  .lift gobjSectionFieldsFormat GobjSection.toFields

/-- Serialize one canonical section entry. -/
def writeGobjSection (entry : GobjSection) : Std.Logical.ByteArray :=
  writeU32LengthPrefixedBytes entry.name ++
  writeByte entry.alignment.bits ++
  writeByte entry.permissions.bits ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeU32LengthPrefixedBytes entry.contents

/-- The independent public section format denotes exactly the canonical writer
prefix with an arbitrary suffix retained. -/
theorem derives_gobjSection_iff {input rest : Std.Logical.ByteArray}
    {entry : GobjSection} :
    Derives gobjSectionFormat input entry rest ↔
      input = writeGobjSection entry ++ rest := by
  constructor
  · intro derivation
    have canonical := derives_gobjSectionFields_iff.mp derivation.lift_inner
    simpa [GobjSection.toFields, writeGobjSectionFields, writeGobjSection,
      Vec.append_assoc] using canonical
  · intro canonical
    apply Derives.lift
    apply derives_gobjSectionFields_iff.mpr
    simpa [GobjSection.toFields, writeGobjSectionFields, writeGobjSection,
      Vec.append_assoc] using canonical

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
                match readU32LengthPrefixedBytes afterReserved with
                | .done contents suffix =>
                  .done { name, alignment, permissions, contents } suffix
                | .needMore hint => .needMore hint
                | .invalid error => .invalid error
              else
                .invalid (.malformed
                  "nonzero .gobj section reserved field")
            | .needMore hint => .needMore hint
            | .invalid error => .invalid error
          | .error error => .invalid error
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .error error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Arbitrary successful section parsing is equivalent to the independent
section-entry format derivation. -/
theorem readGobjSection_done_iff (input : Std.Logical.ByteArray)
    (entry : GobjSection) (rest : Std.Logical.ByteArray) :
    readGobjSection input = .done entry rest ↔
      Derives gobjSectionFormat input entry rest := by
  rw [derives_gobjSection_iff]
  constructor
  · intro parsed
    unfold readGobjSection at parsed
    split at parsed
    next name afterName nameParsed =>
      split at parsed
      next alignmentBits afterAlignment alignmentBitsParsed =>
        split at parsed
        next alignment alignmentDecoded =>
          split at parsed
          next permissionBits afterPermissions permissionBitsParsed =>
            split at parsed
            next permissions permissionsDecoded =>
              split at parsed
              next reserved afterReserved reservedParsed =>
                split at parsed
                next reservedOk =>
                  split at parsed
                  next contents suffix contentsParsed =>
                    injection parsed with entryEq restEq
                    subst entry
                    subst rest
                    have nameInput := derives_u32LengthPrefixedBytes_iff.mp
                      ((readU32LengthPrefixedBytes_done_iff input name
                        afterName).mp nameParsed)
                    have alignmentInput :=
                      (takeByte_realizes.successSound afterName alignmentBits
                        afterAlignment alignmentBitsParsed).byteInput
                    have permissionsInput :=
                      (takeByte_realizes.successSound afterAlignment
                        permissionBits afterPermissions
                        permissionBitsParsed).byteInput
                    have reservedInput := derives_littleEndianFormat_iff.mp
                      ((takeLittleEndian_realizes 2).successSound
                        afterPermissions reserved afterReserved reservedParsed)
                    have contentsInput :=
                      derives_u32LengthPrefixedBytes_iff.mp
                        ((readU32LengthPrefixedBytes_done_iff afterReserved
                          contents suffix).mp contentsParsed)
                    have alignmentOk :=
                      (readGobjSectionAlignment_ok_iff alignmentBits
                        alignment).mp alignmentDecoded
                    have permissionsOk :=
                      (readGobjSectionPermissions_ok_iff permissionBits
                        permissions).mp permissionsDecoded
                    have alignmentBytes : afterName =
                        writeByte alignment.bits ++ afterAlignment := by
                      rw [alignmentOk] at alignmentInput
                      simpa [writeByte] using alignmentInput
                    have permissionsBytes : afterAlignment =
                        writeByte permissions.bits ++ afterPermissions := by
                      rw [permissionsOk] at permissionsInput
                      simpa [writeByte] using permissionsInput
                    calc
                      input = writeU32LengthPrefixedBytes name ++ afterName :=
                        nameInput
                      _ = writeU32LengthPrefixedBytes name ++
                          (writeByte alignment.bits ++ afterAlignment) := by
                        rw [alignmentBytes]
                      _ = writeU32LengthPrefixedBytes name ++
                          (writeByte alignment.bits ++
                              (writeByte permissions.bits ++ afterPermissions)) := by
                        rw [permissionsBytes]
                      _ = writeU32LengthPrefixedBytes name ++
                          (writeByte alignment.bits ++
                            (writeByte permissions.bits ++
                              (writeLittleEndian (count := 2)
                                (0 : BitVec 16) ++ afterReserved))) := by
                        rw [reservedInput, reservedOk]
                      _ = writeGobjSection {
                          name := name
                          alignment := alignment
                          permissions := permissions
                          contents := contents } ++ suffix := by
                        rw [contentsInput]
                        simp [writeGobjSection, Vec.append_assoc]
                  all_goals contradiction
                next => contradiction
              all_goals contradiction
            next => contradiction
          all_goals contradiction
        next => contradiction
      all_goals contradiction
    all_goals contradiction
  · intro canonical
    rw [canonical]
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
    rw [readU32LengthPrefixedBytes_write_append]

/-- `length_writeGobjSection` gives the exact section-entry width. -/
@[simp] theorem length_writeGobjSection (entry : GobjSection) :
    (writeGobjSection entry).length =
      12 + entry.name.bytes.length + entry.contents.bytes.length := by
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
  rw [readU32LengthPrefixedBytes_write_append]

/-- `readGobjSection_write` is the complete-input section round trip. -/
@[simp] theorem readGobjSection_write (entry : GobjSection) :
    readGobjSection (writeGobjSection entry) = .done entry Vec.empty := by
  simpa using readGobjSection_write_append entry Vec.empty

/-- The independent section-entry language has one value and suffix for each
input. -/
theorem gobjSection_derives_deterministic
    {input : Std.Logical.ByteArray} {firstValue secondValue : GobjSection}
    {firstRest secondRest : Std.Logical.ByteArray}
    (first : Derives gobjSectionFormat input firstValue firstRest)
    (second : Derives gobjSectionFormat input secondValue secondRest) :
    firstValue = secondValue ∧ firstRest = secondRest := by
  have firstParsed :=
    (readGobjSection_done_iff input firstValue firstRest).mpr first
  have secondParsed :=
    (readGobjSection_done_iff input secondValue secondRest).mpr second
  rw [firstParsed] at secondParsed
  injection secondParsed with valueEq restEq
  exact ⟨valueEq, restEq⟩

/-- Every successful section parse consumes its complete nonempty canonical
entry prefix and returns precisely the remaining suffix. -/
theorem readGobjSection_success_progress {input : Std.Logical.ByteArray}
    {entry : GobjSection} {rest : Std.Logical.ByteArray}
    (parsed : readGobjSection input = .done entry rest) :
    ∃ consumed, input = consumed ++ rest ∧ 0 < consumed.length := by
  have canonical := derives_gobjSection_iff.mp
    ((readGobjSection_done_iff input entry rest).mp parsed)
  refine ⟨writeGobjSection entry, canonical, ?_⟩
  simp [writeGobjSection, writeByte]
  omega

/-- Canonical deterministic semantics for the `.gobj` section-entry
language. -/
noncomputable def gobjSectionSemantics :
    FormatSemantics gobjSectionFormat :=
  deterministicPrefixSemantics gobjSectionFormat
    gobjSection_derives_deterministic

/-- The section writer realizes the independently defined deterministic entry
semantics. -/
theorem writeGobjSection_realizes :
    WriterRealizes gobjSectionSemantics writeGobjSection := by
  constructor
  · intro entry
    simpa using (derives_gobjSection_iff (entry := entry)
      (rest := Vec.empty)).mpr (by simp)
  · intro entry
    change Derives gobjSectionFormat (writeGobjSection entry) entry Vec.empty
    simpa using (derives_gobjSection_iff (entry := entry)
      (rest := Vec.empty)).mpr (by simp)

/-- Serialize section entries consecutively in their canonical source order. -/
def writeGobjSectionList : List GobjSection → Std.Logical.ByteArray
  | [] => Vec.empty
  | entry :: entries => writeGobjSection entry ++ writeGobjSectionList entries

/-- Total canonical byte width of a section-entry list. -/
def gobjSectionListLength : List GobjSection → Nat
  | [] => 0
  | entry :: entries =>
    12 + entry.name.bytes.length + entry.contents.bytes.length +
      gobjSectionListLength entries

/-- The recursive section-list writer has its exact declared width. -/
@[simp] theorem length_writeGobjSectionList (entries : List GobjSection) :
    (writeGobjSectionList entries).length = gobjSectionListLength entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp [writeGobjSectionList, gobjSectionListLength, ih]

/-- Every encoded section entry contributes at least its 12-byte framing. -/
theorem minLength_gobjSectionList (entries : List GobjSection) :
    12 * entries.length ≤ gobjSectionListLength entries := by
  induction entries with
  | nil => simp [gobjSectionListLength]
  | cons entry entries ih =>
      simp only [List.length_cons, gobjSectionListLength]
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
    | .needMore hint => .needMore hint
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

/-- Parse a section table after checking its minimum possible byte extent. -/
def readGobjSectionTable (input : Std.Logical.ByteArray) :
    ParseResult GobjSectionTable :=
  match takeLittleEndian 4 input with
  | .done count rest =>
    if _minimumFits : 12 * count.toNat ≤ rest.length then
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
    else
      .needMore (some (12 * count.toNat - rest.length))
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
  have minimumFits :
      12 * (BitVec.ofNat 32 table.entries.length).toNat ≤
        (writeGobjSectionList table.entries.toList ++ suffix).length := by
    rw [countEq, Vec.length_append, length_writeGobjSectionList]
    change 12 * table.entries.toList.length ≤
      gobjSectionListLength table.entries.toList + suffix.length
    exact Nat.le_trans (minLength_gobjSectionList table.entries.toList)
      (Nat.le_add_right _ _)
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
  rw [dif_pos minimumFits]
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
