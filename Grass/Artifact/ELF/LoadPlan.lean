import Grass.Artifact.ELF.Header
import Grass.Artifact.ELF.ProgramHeader
import Grass.Memory.Authority

/-! A checked, fixed-address ELF64 load plan. This selected profile accepts
ET_EXEC with PT_LOAD/PT_NULL only. It describes exact logical segment bytes,
not page-table installation, interpreter/relocation processing or OS adequacy.
Authority: https://gabi.xinuos.com/elf/07-pheader.html (2026-09-09).
-/

namespace Grass.Artifact.ELF
open Grass.Std.Logical Grass.Grammar Grass.Artifact.Binary

/-- Explicit format/address/resource selection, not an observed hardware snapshot. -/
structure LoadProfile where
  machine : BitVec 16
  pageSize : Nat
  userStart : Nat
  userLimit : Nat
  maxMappedBytes : Nat
deriving DecidableEq, Repr

def PowerOfTwo (n : Nat) : Prop := 0 < n ∧ n &&& (n - 1) = 0
instance (n : Nat) : Decidable (PowerOfTwo n) := by unfold PowerOfTwo; infer_instance

def LoadProfile.Valid (profile : LoadProfile) : Prop :=
  PowerOfTwo profile.pageSize ∧ profile.userStart < profile.userLimit ∧
  profile.userLimit ≤ 2 ^ 64
instance (profile : LoadProfile) : Decidable profile.Valid := by
  unfold LoadProfile.Valid; infer_instance

/-- Count comes from the same parsed ELF header, never a parallel segment manifest. -/
def readProgramHeaders : Nat → Std.Logical.ByteArray → ParseResult (List ProgramHeader64)
  | 0, input => .done [] input
  | count + 1, input =>
    continueRead (readProgramHeader64 input) fun header rest =>
    continueRead (readProgramHeaders count rest) fun headers rest => .done (header :: headers) rest

/-- Exact file interpretation, retaining both parser receipts and table suffix. -/
structure ParsedImage (bytes : Std.Logical.ByteArray) where
  header : Header64
  headerRest : Std.Logical.ByteArray
  headerRead : readHeader64 bytes = .done header headerRest
  programs : List ProgramHeader64
  tableRest : Std.Logical.ByteArray
  tableRead : readProgramHeaders header.programCount.toNat
    (bytes.drop header.programOffset.toNat) = .done programs tableRest

def parseImage? (bytes : Std.Logical.ByteArray) : Option (ParsedImage bytes) :=
  match h : readHeader64 bytes with
  | .done header headerRest =>
    if header.programEntrySize ≠ 56 ∨ header.programCount.toNat = 65535 ∨
        header.programOffset.toNat + 56 * header.programCount.toNat > bytes.length then none else
    match t : readProgramHeaders header.programCount.toNat (bytes.drop header.programOffset.toNat) with
    | .done programs tableRest => some ⟨header, headerRest, h, programs, tableRest, t⟩
    | _ => none
  | _ => none

def loadSegments {bytes : Std.Logical.ByteArray} (image : ParsedImage bytes) : List ProgramHeader64 :=
  image.programs.filter (fun segment => segment.segmentType == 1)

/-- Exact flag interpretation is selected; real MMU permissions need separate evidence. -/
def segmentPermission (flags : BitVec 32) : Grass.Memory.Permission :=
  { read := flags &&& 4 != 0, write := flags &&& 2 != 0, execute := flags &&& 1 != 0 }

def SegmentValid (profile : LoadProfile) (bytes : Std.Logical.ByteArray) (s : ProgramHeader64) : Prop :=
  s.fileSize.toNat ≤ s.memorySize.toNat ∧
  s.offset.toNat + s.fileSize.toNat ≤ bytes.length ∧
  profile.userStart ≤ s.virtualAddress.toNat ∧
  s.virtualAddress.toNat + s.memorySize.toNat ≤ profile.userLimit ∧
  s.flags.toNat ≤ 7 ∧
  s.virtualAddress.toNat % profile.pageSize = s.offset.toNat % profile.pageSize ∧
  (s.alignment.toNat = 0 ∨ s.alignment.toNat = 1 ∨
    (PowerOfTwo s.alignment.toNat ∧
      s.virtualAddress.toNat % s.alignment.toNat = s.offset.toNat % s.alignment.toNat))
instance (profile : LoadProfile) (bytes : Std.Logical.ByteArray) (s : ProgramHeader64) :
    Decidable (SegmentValid profile bytes s) := by unfold SegmentValid; infer_instance

/-- File bytes followed by the defined zero-filled tail. The checked extent
prevents a short file slice from silently becoming a valid initialized segment. -/
def segmentBytes (bytes : Std.Logical.ByteArray) (s : ProgramHeader64) : Std.Logical.ByteArray :=
  (bytes.drop s.offset.toNat).take s.fileSize.toNat ++
    Vec.replicate (s.memorySize.toNat - s.fileSize.toNat) 0

theorem segmentBytes_length {profile : LoadProfile} {bytes : Std.Logical.ByteArray} {s : ProgramHeader64}
    (valid : SegmentValid profile bytes s) : (segmentBytes bytes s).length = s.memorySize.toNat := by
  have fits := valid.2.1
  have sizes := valid.1
  simp only [segmentBytes, Vec.length_append, Vec.length_take, Vec.length_drop, Vec.length_replicate]
  omega

theorem segmentBytes_file {bytes : Std.Logical.ByteArray} {s : ProgramHeader64} {offset : Nat}
    (inside : offset < s.fileSize.toNat)
    (fits : s.offset.toNat + s.fileSize.toNat ≤ bytes.length) :
    (segmentBytes bytes s).get? offset = bytes.get? (s.offset.toNat + offset) := by
  have bound : offset < ((bytes.drop s.offset.toNat).take s.fileSize.toNat).length := by
    simp only [Vec.length_take, Vec.length_drop]; omega
  rw [segmentBytes, Vec.get?_append_left bound, Vec.get?_take, if_pos inside, Vec.get?_drop]

theorem segmentBytes_zero {bytes : Std.Logical.ByteArray} {s : ProgramHeader64} {offset : Nat}
    (fits : s.offset.toNat + s.fileSize.toNat ≤ bytes.length)
    (tail : s.fileSize.toNat ≤ offset) (inside : offset < s.memorySize.toNat) :
    (segmentBytes bytes s).get? offset = some 0 := by
  have length : ((bytes.drop s.offset.toNat).take s.fileSize.toNat).length = s.fileSize.toNat := by
    simp only [Vec.length_take, Vec.length_drop]; omega
  rw [segmentBytes, Vec.get?_append_right (by omega), length]
  simp [Vec.get?, Vec.replicate, show offset - s.fileSize.toNat < s.memorySize.toNat - s.fileSize.toNat by omega]

def ImageValid (profile : LoadProfile) {bytes : Std.Logical.ByteArray} (image : ParsedImage bytes) : Prop :=
  profile.Valid ∧ image.header.objectType = 2 ∧ image.header.machine = profile.machine ∧
  image.header.flags = 0 ∧ image.header.programEntrySize = 56 ∧
  0 < image.header.programCount.toNat ∧ image.header.programCount.toNat < 65535 ∧
  64 ≤ image.header.programOffset.toNat ∧
  image.header.programOffset.toNat + 56 * image.header.programCount.toNat ≤ bytes.length ∧
  (∀ s ∈ image.programs, s.segmentType = 0 ∨ s.segmentType = 1) ∧
  (∀ s ∈ loadSegments image, SegmentValid profile bytes s) ∧
  (loadSegments image).Pairwise (fun a b =>
    a.virtualAddress.toNat + a.memorySize.toNat ≤ b.virtualAddress.toNat) ∧
  ((loadSegments image).map (fun s => s.memorySize.toNat)).sum ≤ profile.maxMappedBytes ∧
  (∃ s ∈ loadSegments image, (segmentPermission s.flags).execute = true ∧
    s.virtualAddress.toNat ≤ image.header.entry.toNat ∧
    image.header.entry.toNat < s.virtualAddress.toNat + s.memorySize.toNat)
instance (profile : LoadProfile) {bytes : Std.Logical.ByteArray} (image : ParsedImage bytes) :
    Decidable (ImageValid profile image) := by unfold ImageValid; infer_instance

structure LoadPlan (profile : LoadProfile) (bytes : Std.Logical.ByteArray) where
  image : ParsedImage bytes
  valid : ImageValid profile image

/-- Compute and check the interpretation before materializing any zero-fill tail. -/
def plan? (profile : LoadProfile) (bytes : Std.Logical.ByteArray) : Option (LoadPlan profile bytes) := do
  let image ← parseImage? bytes
  if valid : ImageValid profile image then some ⟨image, valid⟩ else none

theorem LoadPlan.segment_valid {profile : LoadProfile} {bytes : Std.Logical.ByteArray}
    (plan : LoadPlan profile bytes) {s : ProgramHeader64} (member : s ∈ loadSegments plan.image) :
    SegmentValid profile bytes s := plan.valid.2.2.2.2.2.2.2.2.2.2.1 s member

end Grass.Artifact.ELF
