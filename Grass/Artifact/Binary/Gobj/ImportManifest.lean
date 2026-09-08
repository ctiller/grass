import Grass.Artifact.Binary.Gobj.Payload

/-!
# Typed `.gobj` import manifest

The manifest gives imported relocation targets a proof-free, structured nominal
identity. Physical loader spellings and derived slots remain outside this object
format layer.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Grammar Grass.Std.Logical

/-- Serializable structured stable identifier; dotted display text is not used. -/
structure GobjNominalId where
  owner : U32LengthPrefixedBytes
  localName : U32LengthPrefixedBytes
deriving DecidableEq, Repr

/-- The exact external subject requested by one object-local import. -/
inductive GobjImportSubject where
  | callable (programSignature exportedCallable : GobjNominalId)
  | provider (providerProfile operation : GobjNominalId)
deriving DecidableEq, Repr

/-- One import keyed by the stable object-local target used by symbols. -/
structure GobjImportEntry where
  localTarget : GobjNominalId
  subject : GobjImportSubject
  abiContract : GobjNominalId
deriving DecidableEq, Repr

/-- Unsigned lexicographic order used by the canonical wire key. -/
def byteListLt : List Byte → List Byte → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | left :: leftRest, right :: rightRest =>
    if left.toNat < right.toNat then true
    else if left = right then byteListLt leftRest rightRest
    else false

/-- Canonical structured encoding of one nominal identifier. -/
def writeGobjNominalId (id : GobjNominalId) : Std.Logical.ByteArray :=
  writeU32LengthPrefixedBytes id.owner ++
    writeU32LengthPrefixedBytes id.localName

theorem minLength_writeGobjNominalId (id : GobjNominalId) :
    8 ≤ (writeGobjNominalId id).length := by
  simp [writeGobjNominalId]
  omega

/-- Parse one structured identifier while retaining the exact suffix. -/
def readGobjNominalId (input : Std.Logical.ByteArray) : ParseResult GobjNominalId :=
  match readU32LengthPrefixedBytes input with
  | .done owner rest =>
    match readU32LengthPrefixedBytes rest with
    | .done localName suffix => .done { owner, localName } suffix
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

@[simp] theorem readGobjNominalId_write_append (id : GobjNominalId)
    (suffix : Std.Logical.ByteArray) :
    readGobjNominalId (writeGobjNominalId id ++ suffix) = .done id suffix := by
  unfold readGobjNominalId writeGobjNominalId
  rw [Vec.append_assoc, readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]

/-- Canonical tagged serialization of an import subject. -/
def writeGobjImportSubject : GobjImportSubject → Std.Logical.ByteArray
  | .callable signature callable =>
    writeByte 0 ++ writeGobjNominalId signature ++ writeGobjNominalId callable
  | .provider profile operation =>
    writeByte 1 ++ writeGobjNominalId profile ++ writeGobjNominalId operation

/-- Parse an import subject and reject unassigned subject tags. -/
def readGobjImportSubject (input : Std.Logical.ByteArray) :
    ParseResult GobjImportSubject :=
  match takeByte input with
  | .done tag rest =>
    if tag = 0 then
      match readGobjNominalId rest with
      | .done signature afterSignature =>
        match readGobjNominalId afterSignature with
        | .done callable suffix => .done (.callable signature callable) suffix
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else if tag = 1 then
      match readGobjNominalId rest with
      | .done profile afterProfile =>
        match readGobjNominalId afterProfile with
        | .done operation suffix => .done (.provider profile operation) suffix
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else .invalid (.malformed "invalid .gobj import subject tag")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

@[simp] theorem readGobjImportSubject_write_append
    (subject : GobjImportSubject) (suffix : Std.Logical.ByteArray) :
    readGobjImportSubject (writeGobjImportSubject subject ++ suffix) =
      .done subject suffix := by
  cases subject with
  | callable signature callable =>
      unfold readGobjImportSubject writeGobjImportSubject
      simp only [Vec.append_assoc]
      rw [takeByte_writeByte_append]
      simp only [ite_true]
      rw [readGobjNominalId_write_append]
      simp only
      rw [readGobjNominalId_write_append]
  | provider profile operation =>
      unfold readGobjImportSubject writeGobjImportSubject
      simp only [Vec.append_assoc]
      rw [takeByte_writeByte_append]
      simp only
      rw [if_neg (by decide : (1 : Byte) ≠ 0)]
      rw [if_pos True.intro]
      rw [readGobjNominalId_write_append]
      simp only
      rw [readGobjNominalId_write_append]

/-- Serialize one complete import entry. -/
def writeGobjImportEntry (entry : GobjImportEntry) : Std.Logical.ByteArray :=
  writeGobjNominalId entry.localTarget ++
    writeGobjImportSubject entry.subject ++
    writeGobjNominalId entry.abiContract

/-- Parse one complete import entry. -/
def readGobjImportEntry (input : Std.Logical.ByteArray) :
    ParseResult GobjImportEntry :=
  match readGobjNominalId input with
  | .done localTarget afterTarget =>
    match readGobjImportSubject afterTarget with
    | .done subject afterSubject =>
      match readGobjNominalId afterSubject with
      | .done abiContract suffix => .done { localTarget, subject, abiContract } suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

@[simp] theorem readGobjImportEntry_write_append (entry : GobjImportEntry)
    (suffix : Std.Logical.ByteArray) :
    readGobjImportEntry (writeGobjImportEntry entry ++ suffix) =
      .done entry suffix := by
  unfold readGobjImportEntry writeGobjImportEntry
  simp only [Vec.append_assoc]
  rw [readGobjNominalId_write_append]
  simp only
  rw [readGobjImportSubject_write_append]
  simp only
  rw [readGobjNominalId_write_append]

/-- Canonical ordering compares the structured identifier encoding. -/
def GobjNominalId.Lt (left right : GobjNominalId) : Prop :=
  byteListLt (writeGobjNominalId left).toList
    (writeGobjNominalId right).toList = true

instance (left right : GobjNominalId) : Decidable (left.Lt right) := by
  unfold GobjNominalId.Lt
  infer_instance

/-- A canonical manifest is a finite map ordered by unique local target. -/
structure GobjImportManifest where
  entries : Vec GobjImportEntry
  countFits : entries.length < 2 ^ 32
  localTargetsUnique :
    (entries.toList.map fun entry => entry.localTarget).Nodup
  canonicallyOrdered :
    (entries.toList.map fun entry => entry.localTarget).Pairwise GobjNominalId.Lt
deriving DecidableEq, Repr

/-- Serialize manifest entries consecutively in canonical key order. -/
def writeGobjImportEntryList : List GobjImportEntry → Std.Logical.ByteArray
  | [] => Vec.empty
  | entry :: rest => writeGobjImportEntry entry ++ writeGobjImportEntryList rest

/-- Parse exactly the declared number of manifest entries. -/
def readGobjImportEntryList : Nat → Std.Logical.ByteArray →
    ParseResult (List GobjImportEntry)
  | 0, input => .done [] input
  | count + 1, input =>
    match readGobjImportEntry input with
    | .done entry rest =>
      match readGobjImportEntryList count rest with
      | .done entries suffix => .done (entry :: entries) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

@[simp] theorem readGobjImportEntryList_write_append
    (entries : List GobjImportEntry) (suffix : Std.Logical.ByteArray) :
    readGobjImportEntryList entries.length
        (writeGobjImportEntryList entries ++ suffix) = .done entries suffix := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.length_cons, writeGobjImportEntryList, Vec.append_assoc,
        readGobjImportEntryList]
      rw [readGobjImportEntry_write_append]
      simp only
      rw [ih]

/-- Every import entry has at least 33 bytes of mandatory framing. -/
theorem minLength_writeGobjImportEntry (entry : GobjImportEntry) :
    33 ≤ (writeGobjImportEntry entry).length := by
  unfold writeGobjImportEntry writeGobjImportSubject writeGobjNominalId
  cases entry.subject <;> simp [writeByte] <;> omega

/-- A list of imports has at least 33 bytes per declared entry. -/
theorem minLength_writeGobjImportEntryList (entries : List GobjImportEntry) :
    33 * entries.length ≤ (writeGobjImportEntryList entries).length := by
  induction entries with
  | nil => simp [writeGobjImportEntryList]
  | cons entry entries ih =>
      simp only [List.length_cons, writeGobjImportEntryList, Vec.length_append]
      have head := minLength_writeGobjImportEntry entry
      omega

/-- Serialize the count and canonical import sequence. -/
def writeGobjImportManifest (manifest : GobjImportManifest) :
    Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (BitVec.ofNat 32 manifest.entries.length) ++
    writeGobjImportEntryList manifest.entries.toList

/-- Parse a manifest and enforce its finite-map canonical form. -/
def readGobjImportManifest (input : Std.Logical.ByteArray) :
    ParseResult GobjImportManifest :=
  match takeLittleEndian 4 input with
  | .done count rest =>
    if _minimumFits : 33 * count.toNat ≤ rest.length then
      match readGobjImportEntryList count.toNat rest with
      | .done entries suffix =>
        if countExact : entries.length = count.toNat then
          if unique : (entries.map fun entry => entry.localTarget).Nodup then
            if ordered : (entries.map fun entry => entry.localTarget).Pairwise
                GobjNominalId.Lt then
              .done {
                entries := Vec.fromList entries
                countFits := by
                  simp only [Vec.length_fromList, countExact]
                  simpa using BitVec.isLt count
                localTargetsUnique := by simpa using unique
                canonicallyOrdered := by simpa using ordered } suffix
            else .invalid (.malformed ".gobj imports are not canonically ordered")
          else .invalid (.malformed "duplicate .gobj import local target")
        else .invalid (.malformed ".gobj import-count mismatch")
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else .needMore (some (33 * count.toNat - rest.length))
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

@[simp] theorem readGobjImportManifest_write_append
    (manifest : GobjImportManifest) (suffix : Std.Logical.ByteArray) :
    readGobjImportManifest (writeGobjImportManifest manifest ++ suffix) =
      .done manifest suffix := by
  have countEq : (BitVec.ofNat 32 manifest.entries.length).toNat =
      manifest.entries.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt manifest.countFits]
  have minimumFits :
      33 * (BitVec.ofNat 32 manifest.entries.length).toNat ≤
        (writeGobjImportEntryList manifest.entries.toList ++ suffix).length := by
    rw [countEq, Vec.length_append]
    exact Nat.le_trans
      (minLength_writeGobjImportEntryList manifest.entries.toList)
      (Nat.le_add_right _ _)
  have parsedEntries :
      readGobjImportEntryList
          (BitVec.ofNat 32 manifest.entries.length).toNat
          (writeGobjImportEntryList manifest.entries.toList ++ suffix) =
        .done manifest.entries.toList suffix := by
    rw [countEq]
    exact readGobjImportEntryList_write_append manifest.entries.toList suffix
  have countExact : manifest.entries.toList.length =
      (BitVec.ofNat 32 manifest.entries.length).toNat := by
    rw [countEq]
    rfl
  unfold readGobjImportManifest writeGobjImportManifest
  rw [Vec.append_assoc, takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [dif_pos minimumFits]
  rw [parsedEntries]
  simp only
  rw [dif_pos countExact, dif_pos manifest.localTargetsUnique,
    dif_pos manifest.canonicallyOrdered]

@[simp] theorem readGobjImportManifest_write (manifest : GobjImportManifest) :
    readGobjImportManifest (writeGobjImportManifest manifest) =
      .done manifest Vec.empty := by
  simpa using readGobjImportManifest_write_append manifest Vec.empty

/-- Frame a typed import manifest for the `.gobj` envelope. -/
def GobjImportManifest.toFramed (manifest : GobjImportManifest)
    (lengthFits : (writeGobjImportManifest manifest).length < 2 ^ 32) :
    U32LengthPrefixedBytes := ⟨writeGobjImportManifest manifest, lengthFits⟩

/-- Parse one exact framed import-manifest body. -/
def parseGobjImportManifestBody (body : U32LengthPrefixedBytes) :
    Except ParseError GobjImportManifest :=
  match readGobjImportManifest body.bytes with
  | .done manifest rest =>
    if rest = Vec.empty then .ok manifest else .error .trailingInput
  | .needMore _ => .error (.malformed "truncated .gobj import-manifest body")
  | .invalid error => .error error

@[simp] theorem parseGobjImportManifestBody_toFramed
    (manifest : GobjImportManifest)
    (lengthFits : (writeGobjImportManifest manifest).length < 2 ^ 32) :
    parseGobjImportManifestBody (manifest.toFramed lengthFits) = .ok manifest := by
  unfold parseGobjImportManifestBody GobjImportManifest.toFramed
  rw [readGobjImportManifest_write]
  rfl

/-- Decode the typed manifest retained in a raw payload envelope. -/
def GobjPayload.parseImports (payload : GobjPayload) :
    Except ParseError GobjImportManifest :=
  parseGobjImportManifestBody payload.imports

/-- Replace only the envelope's import body with a canonical typed manifest. -/
def GobjPayload.withImportManifest (payload : GobjPayload)
    (manifest : GobjImportManifest)
    (lengthFits : (writeGobjImportManifest manifest).length < 2 ^ 32) :
    GobjPayload := { payload with imports := manifest.toFramed lengthFits }

@[simp] theorem GobjPayload.parseImports_withImportManifest
    (payload : GobjPayload) (manifest : GobjImportManifest)
    (lengthFits : (writeGobjImportManifest manifest).length < 2 ^ 32) :
    (payload.withImportManifest manifest lengthFits).parseImports = .ok manifest :=
  parseGobjImportManifestBody_toFramed manifest lengthFits

end Grass.Artifact.Binary.Gobj
