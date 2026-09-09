import Grass.Assembly.SourceLoadedImage
import Grass.Platform.Win32.LoadedAccess

/-! Identify the loader's searched code root with the exact source-bound region.
This establishes storage provenance at a supplied instruction address, not
reachability of that address or a complete fetch. -/

namespace Grass.Assembly.LoadedCodeRoot

open Grass.Std.Logical Grass.Memory Grass.Artifact
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

/-- The checked loader placement makes every selected source-code byte's
allocation-local address nonwrapping. -/
theorem codeRegion_address {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {offset : Nat} {byte : Byte}
    (sourceByte : source.bytes.get? offset = some byte) :
    (addressOf (SourceLoadedImage.codeRegion binding loaded).region.base offset).toNat =
      (SourceLoadedImage.codeRegion binding loaded).region.base.toNat + offset := by
  let selected := SourceLoadedImage.codeRegion binding loaded
  change (addressOf selected.region.base offset).toNat = _
  have present := (loaded.imagePresent selected.region selected.member).1
  have entryMember := Grass.Std.Logical.FiniteMap.mem_of_lookup present
  have valid := loaded.placement.2.1
    (selected.region.allocId, selected.region.allocationRecord) entryMember
  have fits : FitsAllocation selected.region.base selected.region.bytes.length := by
    simpa [CpuPlacementValid, InitializedRegion.allocationRecord] using valid
  have offsetBound : offset < selected.region.bytes.length := by
    have sourceBound := (Vec.get?_isSome_iff source.bytes offset).mp (by simp [sourceByte])
    simpa [selected.bytesExact, length_patchContents] using sourceBound
  exact toNat_addressOf fits offsetBound

/-- An executable selected section contains each exact source byte at its
checked allocation-local address. -/
theorem codeRegion_contains {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs)
    (executable : (sectionPermission binding.placedSection.source.characteristics).execute = true)
    {offset : Nat} {byte : Byte} (sourceByte : source.bytes.get? offset = some byte) :
    ContainsCodeAddress (SourceLoadedImage.codeRegion binding loaded).region
      (addressOf (SourceLoadedImage.codeRegion binding loaded).region.base offset) := by
  let selected := SourceLoadedImage.codeRegion binding loaded
  change ContainsCodeAddress selected.region (addressOf selected.region.base offset)
  have sourceBound := (Vec.get?_isSome_iff source.bytes offset).mp (by simp [sourceByte])
  have offsetBound : offset < selected.region.bytes.length := by
    simpa [selected.bytesExact, length_patchContents] using sourceBound
  have natural := codeRegion_address binding loaded sourceByte
  change (addressOf selected.region.base offset).toNat =
    selected.region.base.toNat + offset at natural
  unfold ContainsCodeAddress
  refine ⟨(congrArg Permission.execute selected.permissionExact).trans executable, ?_, ?_⟩
  · rw [natural]
    omega
  · rw [natural]
    omega

private theorem region_eq_of_contains {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {left right : InitializedRegion}
    (leftMember : left ∈ assignedRegions image inputs loaded.patches)
    (rightMember : right ∈ assignedRegions image inputs loaded.patches)
    {address : MachineAddress} (leftContains : ContainsCodeAddress left address)
    (rightContains : ContainsCodeAddress right address) : left = right := by
  have leftPresent := loaded.imagePresent left leftMember
  have rightPresent := loaded.imagePresent right rightMember
  have sameId : left.allocId = right.allocId := by
    by_cases same : left.allocId = right.allocId
    · exact same
    · exfalso
      have separated := loaded.placement.2.2
        (left.allocId, left.allocationRecord)
        (Grass.Std.Logical.FiniteMap.mem_of_lookup leftPresent.1)
        (right.allocId, right.allocationRecord)
        (Grass.Std.Logical.FiniteMap.mem_of_lookup rightPresent.1)
      have disjoint := separated same
      simp [InitializedRegion.allocationRecord] at disjoint
      unfold ContainsCodeAddress at leftContains rightContains
      omega
  have allocationEq : left.allocationRecord = right.allocationRecord := by
    rw [sameId] at leftPresent
    exact Option.some.inj (leftPresent.1.symm.trans rightPresent.1)
  have storageId : left.storageId = right.storageId := by
    simpa [InitializedRegion.allocationRecord] using
      congrArg AllocationRecord.backing allocationEq
  have backingEq : left.backingRecord = right.backingRecord := by
    rw [storageId] at leftPresent
    exact Option.some.inj (leftPresent.2.symm.trans rightPresent.2)
  have lengths : left.bytes.length = right.bytes.length := by
    simpa [InitializedRegion.backingRecord] using
      congrArg BackingRecord.capacity backingEq
  have stores : ByteStore.empty.write 0 left.bytes.toList true =
      ByteStore.empty.write 0 right.bytes.toList true := by
    simpa [InitializedRegion.backingRecord] using congrArg BackingRecord.bytes backingEq
  have bytesEq : left.bytes = right.bytes := by
    apply Vec.ext_of_get?
    intro index
    change left.bytes.toList[index]? = right.bytes.toList[index]?
    by_cases bounded : index < left.bytes.length
    · have rightBound : index < right.bytes.length := by
        rwa [← lengths]
      have cells := congrArg (fun store : ByteStore => store.cellAt? index)
        stores
      have leftCovered : (ByteRange.mk 0 left.bytes.toList.length).Covers index := by
        exact ⟨Nat.zero_le _, by simpa [Vec.length] using bounded⟩
      have rightCovered : (ByteRange.mk 0 right.bytes.toList.length).Covers index := by
        exact ⟨Nat.zero_le _, by simpa [Vec.length] using rightBound⟩
      rw [ByteStore.cellAt?_write_of_covers _ leftCovered,
        ByteStore.cellAt?_write_of_covers _ rightCovered] at cells
      cases leftAt : left.bytes.toList[index]? <;>
        cases rightAt : right.bytes.toList[index]? <;> simp [leftAt, rightAt] at cells ⊢
      exact cells
    · have rightUnbounded : ¬ index < right.bytes.length := by
        rwa [← lengths]
      rw [List.getElem?_eq_none (Nat.le_of_not_gt (by simpa [Vec.length] using bounded)),
        List.getElem?_eq_none (Nat.le_of_not_gt (by simpa [Vec.length] using rightUnbounded))]
  cases left
  cases right
  simp [InitializedRegion.allocationRecord] at allocationEq sameId storageId bytesEq ⊢
  simp_all

/-- Membership of the exact source region makes the deterministic loader code
root search succeed; no caller-supplied root is needed for admission. -/
theorem codeRoot?_isSome {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {address : MachineAddress}
    (sourceContains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region address) :
    (loaded.codeRoot? address).isSome = true := by
  unfold LoadedImage.codeRoot?
  split
  · rename_i found
    have absent := List.find?_eq_none.mp found
      (SourceLoadedImage.codeRegion binding loaded).region
      (SourceLoadedImage.codeRegion binding loaded).member
    exact (absent (by simpa using sourceContains)).elim
  · rfl

/-- A successful code-root search at an address inside the exact source code
region returns that computed region, rather than another loaded allocation. -/
theorem codeRoot?_region {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {address : MachineAddress}
    (sourceContains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region address)
    {root : CodeRoot loaded address} (_selected : loaded.codeRoot? address = some root) :
    root.region = (SourceLoadedImage.codeRegion binding loaded).region := by
  exact region_eq_of_contains loaded root.member
    (SourceLoadedImage.codeRegion binding loaded).member root.contains sourceContains

/-- The returned code provenance has the exact source-region allocation root. -/
theorem codeRoot?_provenance_root {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {address : MachineAddress}
    (sourceContains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region address)
    {root : CodeRoot loaded address} (selected : loaded.codeRoot? address = some root) :
    root.provenance.root =
      (SourceLoadedImage.codeRegion binding loaded).region.allocId := by
  rw [CodeRoot.provenance, allocationProvenance,
    codeRoot?_region binding loaded sourceContains selected]

end Grass.Assembly.LoadedCodeRoot
