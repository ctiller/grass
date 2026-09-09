import Grass.Assembly.SourceImage
import Grass.Platform.Win32.LoaderEntry

/-! Checked composition facts between resolved source code and the preferred-base
loader result. These facts do not establish entry reachability, ASLR coverage,
or physical loader correspondence. -/

namespace Grass.Assembly.SourceLoadedImage

open Grass.Std.Logical Grass.Memory Grass.Artifact
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

private theorem getElem?_zip_of_eq_some {α β : Type} {xs : List α} {ys : List β}
    {index : Nat} {x : α} {y : β} (hx : xs[index]? = some x)
    (hy : ys[index]? = some y) : (xs.zip ys)[index]? = some (x, y) := by
  induction xs generalizing ys index with
  | nil => simp at hx
  | cons head tail ih =>
      cases ys with
      | nil => simp at hy
      | cons other rest =>
          cases index with
          | zero => simp at hx hy ⊢; exact ⟨hx, hy⟩
          | succ index =>
              simp only [List.getElem?_cons_succ] at hx hy ⊢
              exact ih hx hy

/-- Selecting the exact bound code-section start as the image entry gives the
initial natural RIP from the preferred base and source resolver's code base. -/
theorem entry_rip_exact {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs)
    (entry : image.plan.layout.requested.entryPoint = ⟨sectionIndex, 0⟩) :
    loaded.initialState.rip.toNat =
      (preferredBase image).toNat + source.codeBase := by
  rw [loaded.entryRip_exact, binding.entry_rva entry]

/-- `patchContents_get?_outside` preserves each logical byte outside all IAT slots. -/
theorem patchContents_get?_outside (patches : List ImportPatch) (start : Nat)
    (bytes : Vec Byte) {offset : Nat} {byte : Byte}
    (original : bytes.get? offset = some byte)
    (outside : ∀ patch ∈ patches,
      ¬ (patch.rva ≤ start + offset ∧ start + offset < patch.rva + 8)) :
    (patchContents patches start bytes).get? offset = some byte := by
  have originalList : bytes.toList[offset]? = some byte := by
    simpa [Vec.get?] using original
  simp [patchContents, Vec.get?, originalList,
    patchedByte_outside patches (start + offset) byte outside]

/-- An actual assigned code region exposes each source byte as initialized when
that byte lies outside the exact checked IAT patch slots. `code_byte_initialized`
requires membership in the loaded image's actual assigned regions. -/
theorem code_byte_initialized {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} (loaded : LoadedImage image inputs)
    {region : InitializedRegion}
    (member : region ∈ assignedRegions image inputs loaded.patches)
    (codeBytes : region.bytes =
      patchContents loaded.patches source.codeBase source.bytes)
    {offset : Nat} {byte : Byte} (sourceByte : source.bytes.get? offset = some byte)
    (outside : ∀ patch ∈ loaded.patches,
      ¬ (patch.rva ≤ source.codeBase + offset ∧
        source.codeBase + offset < patch.rva + 8)) :
    loaded.initialState.machine.memory.cellAt? region.allocId offset = some (byte, true) := by
  apply loaded.cellAt? member
  rw [codeBytes]
  exact patchContents_get?_outside loaded.patches source.codeBase source.bytes sourceByte outside

/-- The actual assigned loader region at the algorithmic section position.
The leading image-header region accounts for the successor index. -/
structure CodeRegion {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) where
  private mk ::
  index : Nat
  region : InitializedRegion
  indexExact : index = sectionIndex + 1
  selected : (assignedRegions image inputs loaded.patches)[index]? = some region
  member : region ∈ assignedRegions image inputs loaded.patches
  bytesExact : region.bytes =
    patchContents loaded.patches source.codeBase source.bytes
  permissionExact : region.permission =
    sectionPermission binding.placedSection.source.characteristics
  baseExact : region.base = BitVec.ofNat 64
    ((preferredBase image).toNat + source.codeBase)

/-- Select the code region from the exact placed-section and identity lists. -/
def codeRegion {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) : CodeRegion binding loaded := by
  have sectionBound : sectionIndex < image.plan.layout.placed.length := by
    exact (Vec.get?_isSome_iff image.plan.layout.placed sectionIndex).mp
      (by simp [binding.selected])
  have imageLength : (imageRegions image.plan loaded.patches).length =
      image.plan.layout.placed.length + 1 := by
    simp [imageRegions, Vec.length]
  have identityBound : sectionIndex + 1 < inputs.identities.length := by
    rw [loaded.identitiesComplete, imageLength]
    omega
  let identity := inputs.identities[sectionIndex + 1]'identityBound
  let region : InitializedRegion :=
    { allocId := identity.allocation
      storageId := identity.storage
      epoch := identity.epoch
      base := BitVec.ofNat 64 ((preferredBase image).toNat + source.codeBase)
      permission := sectionPermission binding.placedSection.source.characteristics
      source := .imageMapping
      owner := inputs.thread
      bytes := patchContents loaded.patches source.codeBase source.bytes }
  have placedAt : image.plan.layout.placed.toList[sectionIndex]? =
      some binding.placedSection := binding.selected
  let codeView : ImageRegion :=
    { rva := source.codeBase
      bytes := patchContents loaded.patches source.codeBase source.bytes
      permission := sectionPermission binding.placedSection.source.characteristics }
  have imageAt : (imageRegions image.plan loaded.patches)[sectionIndex + 1]? = some codeView := by
    simp [imageRegions, placedAt, codeView, binding.baseExact, binding.bytesExact]
  have identityAt : inputs.identities[sectionIndex + 1]? = some identity :=
    List.getElem?_eq_getElem identityBound
  have zipAt : ((imageRegions image.plan loaded.patches).zip inputs.identities)[sectionIndex + 1]? =
      some (codeView, identity) := by
    exact getElem?_zip_of_eq_some imageAt identityAt
  have assignedAt :
      (assignedRegions image inputs loaded.patches)[sectionIndex + 1]? = some region := by
    simp [assignedRegions, zipAt, region, codeView]
  exact .mk (sectionIndex + 1) region rfl assignedAt
    (List.mem_of_getElem? assignedAt) rfl rfl rfl

/-- Every unpatched source byte is initialized in the deterministically selected
code allocation installed by the loader result. -/
theorem selected_code_byte_initialized {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {offset : Nat} {byte : Byte}
    (sourceByte : source.bytes.get? offset = some byte)
    (outside : ∀ patch ∈ loaded.patches,
      ¬ (patch.rva ≤ source.codeBase + offset ∧
        source.codeBase + offset < patch.rva + 8)) :
    loaded.initialState.machine.memory.cellAt?
      (codeRegion binding loaded).region.allocId offset = some (byte, true) := by
  let selected := codeRegion binding loaded
  exact code_byte_initialized loaded selected.member selected.bytesExact sourceByte outside

end Grass.Assembly.SourceLoadedImage
