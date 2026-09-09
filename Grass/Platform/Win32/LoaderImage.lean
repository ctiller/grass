import Grass.Artifact.PE.ImageWriter
import Grass.Std.Logical.HostBytes
import Grass.Memory.State

/-!
# Exact PE initialization inputs

This is the bounded preferred-base initialization layer, not a Windows loader
adequacy theorem or an ASLR profile. It consumes the checked writer plan; import
targets are environment data. The section views cover logical payloads, not a
claim that physical page tails or gaps are absent from the CPU address space.

Format authority: Microsoft PE Format, "Section Table" and "Import Address
Table", https://learn.microsoft.com/en-us/windows/win32/debug/pe-format.
Physical mapping, DLL initialization, import resolution and applicability to a
particular Windows loader remain external obligations.
-/

namespace Grass.Platform.Win32.Loader

open Grass.Std.Logical Grass.Artifact.Binary Grass.Memory
open Grass.Artifact

/-- The exact host bytes emitted from one checked, instruction-independent plan. -/
structure ImageInput where
  plan : PE.ImagePlan
  bytes : _root_.ByteArray
  bytesExact : bytes = (PE.writeImage plan).toHostBytes

/-- A resolved import address and its derived image-relative eight-byte slot. -/
structure ImportPatch where
  rva : Nat
  target : BitVec 64
deriving DecidableEq, Repr

/-- Target data follows the exact library/symbol order in the checked plan. -/
abbrev ImportTargets := Vec (Vec (BitVec 64))

/-- Derive every slot while refusing missing or extra library/symbol targets. -/
def importPatchesFrom? (baseRva : Nat) :
    List PE.ImportLibraryLayout → List (Vec (BitVec 64)) → Option (List ImportPatch)
  | [], [] => some []
  | library :: libraries, targets :: rest => do
      if targets.length ≠ library.library.symbols.length then none else do
        let tail ← importPatchesFrom? baseRva libraries rest
        pure (targets.toList.zipIdx.map (fun (target, index) =>
          { rva := PE.iatSlotRva baseRva library index, target }) ++ tail)
  | _, _ => none

/-- Resolve import slots only through the plan's materialized import layout. -/
def importPatches? (plan : PE.ImagePlan) (targets : ImportTargets) :
    Option (List ImportPatch) :=
  match plan.layout.importSectionRva with
  | none => if targets.length = 0 ∧ plan.layout.importLayouts.length = 0 then some [] else none
  | some rva => importPatchesFrom? rva plan.layout.importLayouts.toList targets.toList

/-- Observe a resolved QWORD byte only inside that patch's exact slot. -/
def ImportPatch.byteAt? (patch : ImportPatch) (rva : Nat) : Option Byte :=
  if patch.rva ≤ rva ∧ rva < patch.rva + 8 then
    (writeLittleEndian (count := 8) patch.target).get? (rva - patch.rva)
  else none

/-- Ordered patch lookup; the initialization checker also requires disjoint slots. -/
def patchedByte (patches : List ImportPatch) (rva : Nat) (original : Byte) : Byte :=
  match patches with
  | [] => original
  | patch :: tail => (patch.byteAt? rva).getD (patchedByte tail rva original)

/-- Replace only IAT bytes; retain every other payload byte verbatim. -/
def patchContents (patches : List ImportPatch) (start : Nat) (bytes : Vec Byte) : Vec Byte :=
  Vec.fromList (bytes.toList.zipIdx.map (fun (byte, index) =>
    patchedByte patches (start + index) byte))

/-- The patched region has the original byte count. -/
@[simp] theorem length_patchContents (patches : List ImportPatch) (start : Nat)
    (bytes : Vec Byte) : (patchContents patches start bytes).length = bytes.length := by
  simp [patchContents, Vec.length]

/-- Bytes outside every IAT slot are unchanged, independently of target values. -/
theorem patchedByte_outside (patches : List ImportPatch) (rva : Nat) (original : Byte)
    (outside : ∀ patch ∈ patches, ¬ (patch.rva ≤ rva ∧ rva < patch.rva + 8)) :
    patchedByte patches rva original = original := by
  induction patches with
  | nil => rfl
  | cons patch tail ih =>
      have head := outside patch (by simp)
      have rest := ih (fun p hp => outside p (by simp [hp]))
      simp [patchedByte, ImportPatch.byteAt?, head, rest]

/-- One logical image view, with permissions derived from the section flags. -/
structure ImageRegion where
  rva : Nat
  bytes : Vec Byte
  permission : Permission
deriving DecidableEq, Repr

/-- PE section access bits, without inventing atomic-only authority. -/
def sectionPermission (flags : BitVec 32) : Permission :=
  { read := flags &&& 0x40000000 != 0
    write := flags &&& 0x80000000 != 0
    execute := flags &&& 0x20000000 != 0 }

/-- Exact padded headers and logical section contents at the writer's RVAs.
Raw file padding is not asserted to be initialized virtual payload. -/
def imageRegions (plan : PE.ImagePlan) (patches : List ImportPatch) : List ImageRegion :=
  { rva := 0, bytes := PE.writeAlignedHeaders plan.layout, permission := .readOnly } ::
    plan.layout.placed.toList.map (fun placed =>
      { rva := placed.virtualSpan.start
        bytes := patchContents patches placed.virtualSpan.start placed.source.contents
        permission := sectionPermission placed.source.characteristics })

/-- Every computed logical region is bounded by the same plan's image extent. -/
theorem imageRegions_bounded (plan : PE.ImagePlan) (patches : List ImportPatch)
    {region : ImageRegion} (member : region ∈ imageRegions plan patches) :
    region.rva + region.bytes.length ≤ plan.layout.sizeOfImage := by
  rcases List.mem_cons.mp member with head | tail
  · subst region
    simpa using plan.layout.headersWithinImage
  · obtain ⟨placed, present, rfl⟩ := List.mem_map.mp tail
    simp only [length_patchContents]
    have bounded := plan.layout.sectionsWithinImage present
    rw [PE.FileSpan.endOffset, plan.placedVirtualSize present] at bounded
    exact bounded

/-- Patch ranges must be disjoint, wholly inside one logical section, and name
nonzero low-user-half target addresses. Actual export identity is external. -/
def PatchesValid (plan : PE.ImagePlan) (patches : List ImportPatch) : Prop :=
  patches.Pairwise (fun a b => a.rva + 8 ≤ b.rva ∨ b.rva + 8 ≤ a.rva) ∧
  ∀ patch ∈ patches,
    0 < patch.target.toNat ∧ patch.target.toNat < 2 ^ 47 ∧
    ∃ placed ∈ plan.layout.placed.toList,
      placed.virtualSpan.start ≤ patch.rva ∧
      patch.rva + 8 ≤ placed.virtualSpan.start + placed.source.contents.length

instance (plan : PE.ImagePlan) (patches : List ImportPatch) :
    Decidable (PatchesValid plan patches) := by
  unfold PatchesValid
  infer_instance

end Grass.Platform.Win32.Loader
