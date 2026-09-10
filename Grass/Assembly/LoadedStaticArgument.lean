import Grass.Assembly.SourceStaticBindings
import Grass.Platform.Win32.CallMemory
import Grass.Platform.Win32.LoadedAccess
import Grass.Platform.Win32.LoaderEntry

/-! Checked suffix arguments derived from one bound static object and an actual
loaded-image region. This layer identifies bytes and current memory; it does not
claim that an instruction or API call used the resulting address. -/
namespace Grass.Assembly.LoadedStaticArgument

open Grass.Artifact.PE
open Grass.Memory Grass.Std.Logical
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

/-- A checked static-object suffix in current memory. The private constructor
keeps selection, loader correspondence, current resolution, placement, and every
initialized byte behind `prepare?`. -/
structure Prepared {image : ImageInput} {inputs : EntryInputs}
    {table : StaticObjects.Table} {layout : StaticSection.Layout table}
    {sectionIndex : Nat}
    (binding : SourceStaticBindings.Binding image.plan layout sectionIndex)
    (loaded : LoadedImage image inputs) (memory : MemoryState) (offset : Nat) where
  private mk ::
  regionIndex : Nat
  region : InitializedRegion
  regionIndexExact : regionIndex = sectionIndex + 1
  regionSelected : (assignedRegions image inputs loaded.patches)[regionIndex]? = some region
  regionBaseExact : region.base = BitVec.ofNat 64
      ((preferredBase image).toNat + binding.span.placedSection.virtualSpan.start)
  regionBytesExact : region.bytes = patchContents loaded.patches
    binding.span.placedSection.virtualSpan.start binding.span.placedSection.source.contents
  regionPermissionExact : region.permission =
    sectionPermission binding.span.placedSection.source.characteristics
  offsetBound : offset ≤ binding.object.declaration.bytes.length
  loadedPayloadExact :
    (region.bytes.drop (binding.object.offset + offset)).take
      (binding.object.declaration.bytes.length - offset) =
        binding.object.declaration.bytes.drop offset
  provenance : Provenance
  provenanceExact : provenance = allocationProvenance region.allocId region.allocationRecord
  argument : CallMemory.Argument
  argumentExact : argument =
    { provenance := provenance
      range := { start := binding.object.offset + offset
                 size := binding.object.declaration.bytes.length - offset } }
  bytes : Grass.Std.Logical.ByteArray
  bytesExact : bytes = binding.object.declaration.bytes.drop offset
  allocationPresent : memory.allocations.lookup region.allocId = some region.allocationRecord
  resolved : CallMemory.Resolved memory argument
  allocationExact : resolved.allocation = region.allocationRecord
  address : MachineAddress
  addressExact : address = addressOf resolved.base argument.range.start
  addressNat : address.toNat = (preferredBase image).toNat + binding.span.rva + offset
  cellsExact : bytes.toList.zipIdx.all (fun entry => decide
    (memory.cellAt? argument.provenance.root (argument.range.start + entry.2) =
      some (entry.1, true))) = true

/-- Select the loader's exact section region (after the leading header region),
reject changes within the requested suffix or stale current memory, and prepare
the remaining suffix. An offset at the object's exclusive end is valid and yields empty bytes.
Requiring the current allocation record to equal the loader's exact region record
is a conservative applicability check, not a claim that every valid call must retain
that record unchanged. -/
def prepare? {image : ImageInput} {inputs : EntryInputs}
    {table : StaticObjects.Table} {layout : StaticSection.Layout table}
    {sectionIndex : Nat}
    (binding : SourceStaticBindings.Binding image.plan layout sectionIndex)
    (loaded : LoadedImage image inputs) (memory : MemoryState) (offset : Nat) :
    Option (Prepared binding loaded memory offset) := do
  if offsetBound : offset ≤ binding.object.declaration.bytes.length then
    let regionIndex := sectionIndex + 1
    match regionSelected : (assignedRegions image inputs loaded.patches)[regionIndex]? with
    | none => none
    | some region =>
      if regionBaseExact : region.base = BitVec.ofNat 64
          ((preferredBase image).toNat + binding.span.placedSection.virtualSpan.start) then
        if regionBytesExact : region.bytes = patchContents loaded.patches
            binding.span.placedSection.virtualSpan.start
            binding.span.placedSection.source.contents then
          if regionPermissionExact : region.permission =
              sectionPermission binding.span.placedSection.source.characteristics then
    if loadedPayloadExact :
                (region.bytes.drop (binding.object.offset + offset)).take
                  (binding.object.declaration.bytes.length - offset) =
                    binding.object.declaration.bytes.drop offset then
              let provenance := allocationProvenance region.allocId region.allocationRecord
              let argument : CallMemory.Argument :=
                { provenance
                  range := { start := binding.object.offset + offset
                             size := binding.object.declaration.bytes.length - offset } }
              let bytes := binding.object.declaration.bytes.drop offset
              if allocationPresent : memory.allocations.lookup region.allocId =
                  some region.allocationRecord then
                match accessResult : memory.resolveAccess? provenance argument.range with
                | .error _ => none
                | .ok access =>
                  have allocationExact : access.allocation = region.allocationRecord :=
                    Option.some.inj (access.allocationLookup.symm.trans allocationPresent)
                  match placed : access.allocation.base with
                  | none => none
                  | some base =>
                    if noWrap : FitsAllocation base access.allocation.extent.stop then
                      let resolved : CallMemory.Resolved memory argument :=
                        { toResolvedAccess := access, base, placed, noWrap }
                      let address := addressOf base argument.range.start
                      if addressBound : base.toNat + argument.range.start < 2 ^ 64 then
                        if cellsExact : bytes.toList.zipIdx.all (fun entry => decide
                            (memory.cellAt? argument.provenance.root
                              (argument.range.start + entry.2) = some (entry.1, true))) = true then
                          have addressNat : address.toNat = base.toNat + argument.range.start := by
                            unfold address addressOf
                            simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
                            rw [Nat.mod_eq_of_lt (by
                              omega : argument.range.start < 2 ^ 64)]
                            exact Nat.mod_eq_of_lt addressBound
                          have canonicalAddress : address.toNat =
                              (preferredBase image).toNat + binding.span.rva + offset := by
                            rw [addressNat]
                            have allocationBase : region.allocationRecord.base = some base := by
                              rw [← allocationExact]
                              exact placed
                            have baseEq : base = region.base := by
                              simpa [InitializedRegion.allocationRecord] using allocationBase.symm
                            rw [baseEq, regionBaseExact, BitVec.toNat_ofNat]
                            rw [Nat.mod_eq_of_lt]
                            · rw [binding.span.rva_eq]
                              simp only [argument]
                              omega
                            · have imageBound := loaded.entry.1
                              have placedMember : binding.span.placedSection ∈
                                  image.plan.layout.placed.toList :=
                                (Grass.Std.Logical.Vec.mem_iff_exists_get?).mpr
                                  ⟨sectionIndex, binding.span.selected⟩
                              have sectionBound := image.plan.layout.sectionsWithinImage placedMember
                              have objectBound := binding.span.endInBounds
                              rw [Grass.Artifact.PE.FileSpan.endOffset,
                                image.plan.placedVirtualSize placedMember] at sectionBound
                              simp only [StaticSection.Object.endOffset] at objectBound
                              omega
                          some ⟨regionIndex, region, rfl, regionSelected, regionBaseExact,
                            regionBytesExact, regionPermissionExact, offsetBound,
                            loadedPayloadExact, provenance, rfl, argument, rfl, bytes, rfl,
                            allocationPresent, resolved, allocationExact, address, rfl,
                            canonicalAddress, cellsExact⟩
                        else none
                      else none
                    else none
              else none
            else none
          else none
        else none
      else none
  else none

/-- `bytes_eq_remaining` exposes the prepared suffix in the original declaration. -/
theorem Prepared.bytes_eq_remaining {image : ImageInput} {inputs : EntryInputs}
    {table : StaticObjects.Table} {layout : StaticSection.Layout table}
    {sectionIndex : Nat} {binding : SourceStaticBindings.Binding image.plan layout sectionIndex}
    {loaded : LoadedImage image inputs} {memory : MemoryState} {offset : Nat}
    (prepared : Prepared binding loaded memory offset) :
    prepared.bytes = binding.object.declaration.bytes.drop offset :=
  prepared.bytesExact

/-- `Prepared.cells` gives the current initialized byte evidence retained by
`prepare?`, one exact byte at a time. -/
theorem Prepared.cells {image : ImageInput} {inputs : EntryInputs}
    {table : StaticObjects.Table} {layout : StaticSection.Layout table}
    {sectionIndex : Nat} {binding : SourceStaticBindings.Binding image.plan layout sectionIndex}
    {loaded : LoadedImage image inputs} {memory : MemoryState} {offset index : Nat}
    (prepared : Prepared binding loaded memory offset) {byte : Byte}
    (present : prepared.bytes.get? index = some byte) :
    memory.cellAt? prepared.argument.provenance.root
      (prepared.argument.range.start + index) = some (byte, true) := by
  have listPresent : prepared.bytes.toList[index]? = some byte := by
    simpa [Vec.get?] using present
  have indexed : (byte, index) ∈ prepared.bytes.toList.zipIdx := by
    exact List.mem_zipIdx_iff_getElem?.2 listPresent
  exact of_decide_eq_true (List.all_eq_true.mp prepared.cellsExact (byte, index) indexed)

end Grass.Assembly.LoadedStaticArgument
