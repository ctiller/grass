import Grass.Platform.Win32.LoaderImage
import Grass.Platform.Win32.LoaderRegion
import Grass.Artifact.PE.ImageRoundTrip
import Grass.ISA.X86.Execution.State

/-!
# Checked preferred-base entry initialization

The result is a concrete initialization witness in the shared memory/x86 state.
It is an intermediate subprofile, not the canonical Win10 execution contract:
relocated loading, physical page coverage, loader/DLL side effects, API target
identity and complete instruction outcomes still require their own relations.
In particular, accepting these inputs does not establish runtime safety.

Stack geometry follows Microsoft's x64 calling convention:
https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention .
The environment supplies actual stack storage, initialized return bytes, all
register values, context identities and existing history/obligation ledgers.
-/

namespace Grass.Platform.Win32.Loader

open Grass.Core Grass.Memory Grass.Std.Logical Grass.Artifact Grass.ISA.X86

/-- Nominal storage identities supplied from the environment's identity domain. -/
structure RegionIdentity where
  allocation : AllocId
  storage : StorageId
  epoch : EpochId
deriving DecidableEq, Repr

/-- Actual stack view and the source's required window below entry RSP. -/
structure StackInput where
  allocation : AllocId
  offset : Nat
  frameBytes : Nat
  returnAddress : BitVec 64
deriving DecidableEq, Repr

/-- Data supplied by the selected execution environment, with no behavior field. -/
structure EntryInputs where
  environment : MachineState
  thread : ContextId
  independentContext : ContextId
  identities : List RegionIdentity
  targets : ImportTargets
  stack : StackInput
  gpr : Gpr → BitVec 64
  rflags : BitVec 64

/-- Preferred address recovered by the independently checked image reader. -/
def preferredBase (image : ImageInput) : MachineAddress :=
  image.plan.expectedImage.optional.imageBase

/-- Assign exact derived image views to externally supplied fresh identities. -/
def assignedRegions (image : ImageInput) (inputs : EntryInputs)
    (patches : List ImportPatch) : List InitializedRegion :=
  ((imageRegions image.plan patches).zip inputs.identities).map (fun (region, identity) =>
    { allocId := identity.allocation, storageId := identity.storage, epoch := identity.epoch
      base := BitVec.ofNat 64 ((preferredBase image).toNat + region.rva)
      permission := region.permission, source := .imageMapping, owner := inputs.thread
      bytes := region.bytes })

/-- Install all image regions using only the public checked memory doors. -/
def installRegions? (before : MemoryState) : List InitializedRegion → Option MemoryState
  | [] => some before
  | region :: tail => do
      let next ← installInitializedRegion? before region
      installRegions? next tail

/-- An existing allocation lookup survives the complete installation sequence. -/
theorem installRegions?_allocation_preserved {before after : MemoryState}
    {regions : List InitializedRegion} {id : AllocId} {record : AllocationRecord}
    (installed : installRegions? before regions = some after)
    (present : before.allocations.lookup id = some record) :
    after.allocations.lookup id = some record := by
  induction regions generalizing before with
  | nil => simp [installRegions?] at installed; cases installed; exact present
  | cons region tail ih =>
    change (installInitializedRegion? before region).bind (fun next => installRegions? next tail) =
      some after at installed
    obtain ⟨next, head, rest⟩ := Option.bind_eq_some_iff.mp installed
    have different : id ≠ region.allocId := by
      intro same
      have absent := (installInitializedRegion?_admitted head).2.1
      rw [← same, present] at absent
      contradiction
    exact ih rest ((installInitializedRegion?_allocation_ne head different).trans present)

/-- An existing backing lookup survives the complete installation sequence. -/
theorem installRegions?_backing_preserved {before after : MemoryState}
    {regions : List InitializedRegion} {id : StorageId} {record : BackingRecord}
    (installed : installRegions? before regions = some after)
    (present : before.backings.lookup id = some record) :
    after.backings.lookup id = some record := by
  induction regions generalizing before with
  | nil => simp [installRegions?] at installed; cases installed; exact present
  | cons region tail ih =>
    change (installInitializedRegion? before region).bind (fun next => installRegions? next tail) =
      some after at installed
    obtain ⟨next, head, rest⟩ := Option.bind_eq_some_iff.mp installed
    have different : id ≠ region.storageId := by
      intro same
      have absent := (installInitializedRegion?_admitted head).2.2.1
      rw [← same, present] at absent
      contradiction
    exact ih rest ((installInitializedRegion?_backing_ne head different).trans present)

/-- Final authoritative records contain the exact computed payload and permissions. -/
def RegionsPresent (memory : MemoryState) (regions : List InitializedRegion) : Prop :=
  ∀ region ∈ regions,
    memory.allocations.lookup region.allocId = some region.allocationRecord ∧
    memory.backings.lookup region.storageId = some region.backingRecord

instance (memory : MemoryState) (regions : List InitializedRegion) :
    Decidable (RegionsPresent memory regions) := by
  unfold RegionsPresent
  infer_instance

/-- All represented live CPU views have present, nonwrapping, mutually disjoint
placements. This is not a statement that unrepresented physical pages do not exist. -/
def CpuPlacementValid (record : AllocationRecord) : Prop :=
  record.live = true → record.space = .cpuVirtual →
    match record.base with
    | none => False
    | some base => FitsAllocation base record.extent.stop

instance (record : AllocationRecord) : Decidable (CpuPlacementValid record) := by
  unfold CpuPlacementValid
  split <;> infer_instance

/-- Different represented live CPU allocation identities have disjoint addresses. -/
def CpuPlacementsDisjoint (a b : AllocId × AllocationRecord) : Prop :=
    a.1 ≠ b.1 → a.2.live = true → b.2.live = true →
    a.2.space = .cpuVirtual → b.2.space = .cpuVirtual →
    match a.2.base, b.2.base with
    | some baseA, some baseB =>
        baseA.toNat + a.2.extent.stop ≤ baseB.toNat + b.2.extent.start ∨
        baseB.toNat + b.2.extent.stop ≤ baseA.toNat + a.2.extent.start
    | _, _ => True

set_option synthInstance.maxSize 256 in
instance (a b : AllocId × AllocationRecord) : Decidable (CpuPlacementsDisjoint a b) := by
  unfold CpuPlacementsDisjoint
  split <;> infer_instance

/-- Dedicated storage plus nonwrapping and mutually disjoint CPU placements. -/
def PlacementValid (memory : MemoryState) : Prop :=
  memory.DedicatedBackings ∧
  (∀ entry ∈ memory.allocations.entries, CpuPlacementValid entry.2) ∧
  (∀ a ∈ memory.allocations.entries, ∀ b ∈ memory.allocations.entries,
    CpuPlacementsDisjoint a b)

instance (memory : MemoryState) : Decidable (PlacementValid memory) := by
  unfold PlacementValid
  infer_instance

/-- RSP is the exact nonwrapping address of the supplied stack offset. -/
def StackPlacementValid (record : AllocationRecord) (inputs : EntryInputs) : Prop :=
  match record.base with
  | none => False
  | some base => FitsAllocation base record.extent.stop ∧
      (inputs.gpr .rsp).toNat = base.toNat + inputs.stack.offset

instance (record : AllocationRecord) (inputs : EntryInputs) :
    Decidable (StackPlacementValid record inputs) := by
  unfold StackPlacementValid
  split <;> infer_instance

/-- Stack bytes are checked in the existing memory, never invented by initialization.
The caller owns a writable non-executable CPU stack with return slot, home area,
and the requested source frame window. Only return-slot bytes must be initialized. -/
def StackValid (memory : MemoryState) (inputs : EntryInputs) : Prop :=
  ∃ record ∈ memory.allocations.lookup inputs.stack.allocation,
    record.live = true ∧ record.space = .cpuVirtual ∧ record.source = .stack ∧
    inputs.thread ∈ record.owners ∧ record.permission = .readWrite ∧
    record.extent.start + inputs.stack.frameBytes ≤ inputs.stack.offset ∧
    inputs.stack.offset + 40 ≤ record.extent.stop ∧
    StackPlacementValid record inputs ∧
    (inputs.gpr .rsp).toNat % 16 = 8 ∧
    (∀ index ∈ List.range 8,
      memory.cellAt? inputs.stack.allocation (inputs.stack.offset + index) =
        ((Binary.writeLittleEndian (count := 8) inputs.stack.returnAddress).get? index).map
          (fun byte => (byte, true)))

instance (memory : MemoryState) (inputs : EntryInputs) : Decidable (StackValid memory inputs) := by
  unfold StackValid
  infer_instance

/-- Explicit nonempty independent context inventory and the selected ABI's DF
clear condition. Other full RFLAGS bits and all non-RSP registers remain data. -/
def EnvironmentValid (inputs : EntryInputs) : Prop :=
  inputs.environment.contexts.lookup inputs.thread = some .thread ∧
  inputs.independentContext ≠ inputs.thread ∧
  (inputs.environment.contexts.lookup inputs.independentContext).isSome = true ∧
  inputs.rflags &&& 0x402 = 2

instance (inputs : EntryInputs) : Decidable (EnvironmentValid inputs) := by
  unfold EnvironmentValid
  infer_instance

/-- Entry lies inside a non-discardable executable logical section. This does not
claim that a complete first instruction has already passed the x86 fetch check. -/
def EntryMapped (image : ImageInput) : Prop :=
  (preferredBase image).toNat + image.plan.layout.sizeOfImage < 2 ^ 47 ∧
  image.plan.layout.entryPointRva < image.plan.layout.sizeOfImage ∧
  ∃ placed ∈ image.plan.layout.placed.toList,
    placed.virtualSpan.start ≤ image.plan.layout.entryPointRva ∧
    image.plan.layout.entryPointRva < placed.virtualSpan.start + placed.source.contents.length ∧
    (sectionPermission placed.source.characteristics).execute = true ∧
    placed.source.characteristics &&& 0x02000000 = 0

instance (image : ImageInput) : Decidable (EntryMapped image) := by
  unfold EntryMapped
  infer_instance

/-- New image identities do not reuse represented historical provenance or
captured backing identities. Freshness outside the supplied machine's records
remains an environment-domain obligation. -/
def HistoryFresh (machine : MachineState) (regions : List InitializedRegion) : Prop :=
  ∀ region ∈ regions,
    (∀ event ∈ machine.events,
      event.event.provenance.root ≠ region.allocId ∧ event.event.mapping.backing ≠ region.storageId) ∧
    (∀ violation ∈ machine.violations.records?, violation.provenance.root ≠ region.allocId)

instance (machine : MachineState) (regions : List InitializedRegion) :
    Decidable (HistoryFresh machine regions) := by
  unfold HistoryFresh
  infer_instance

/-- Checked initialization facts. There is no caller-defined profile or safety
predicate. Actual Windows loading and admissible ASLR bases are not asserted. -/
structure LoadedImage (image : ImageInput) (inputs : EntryInputs) where
  patches : List ImportPatch
  patchesExact : importPatches? image.plan inputs.targets = some patches
  patchesValid : PatchesValid image.plan patches
  identitiesComplete : inputs.identities.length = (imageRegions image.plan patches).length
  historyFresh : HistoryFresh inputs.environment (assignedRegions image inputs patches)
  memory : MemoryState
  installed : installRegions? inputs.environment.memory (assignedRegions image inputs patches) = some memory
  imagePresent : RegionsPresent memory (assignedRegions image inputs patches)
  placement : PlacementValid memory
  stack : StackValid memory inputs
  environment : EnvironmentValid inputs
  entry : EntryMapped image

/-- Compute all deterministic initialization artifacts, refusing incomplete target
or identity lists, collision, invalid placement, stack, context or entry inputs. -/
def initialize? (image : ImageInput) (inputs : EntryInputs) : Option (LoadedImage image inputs) := do
  match hpatches : importPatches? image.plan inputs.targets with
  | none => none
  | some patches =>
    if hp : PatchesValid image.plan patches then
    if hi : inputs.identities.length = (imageRegions image.plan patches).length then
    if hh : HistoryFresh inputs.environment (assignedRegions image inputs patches) then
      match hmemory : installRegions? inputs.environment.memory (assignedRegions image inputs patches) with
      | none => none
      | some memory =>
        if hr : RegionsPresent memory (assignedRegions image inputs patches) then
        if hl : PlacementValid memory then
        if hs : StackValid memory inputs then
        if he : EnvironmentValid inputs then
        if hm : EntryMapped image then
          some ⟨patches, hpatches, hp, hi, hh, memory, hmemory, hr, hl, hs, he, hm⟩
        else none else none else none else none else none
    else none else none else none

/-- Embed the initialized memory once; retain all actual environment ledgers,
event supply and context bindings. RIP is derived from the same writer plan. -/
def LoadedImage.initialState {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) : Execution.State :=
  { machine := { inputs.environment with memory := loaded.memory }
    gpr := inputs.gpr
    rip := BitVec.ofNat 64 ((preferredBase image).toNat + image.plan.layout.entryPointRva)
    rflags := inputs.rflags }

/-- Replacing memory back recovers the entire supplied machine, including all
history, fault, obligation, violation, supply and context fields. -/
theorem LoadedImage.environment_frame {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    { loaded.initialState.machine with memory := inputs.environment.memory } =
      inputs.environment := rfl

/-- Every byte of a computed image view is initialized in authoritative storage. -/
theorem LoadedImage.cellAt? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {region : InitializedRegion}
    (member : region ∈ assignedRegions image inputs loaded.patches)
    {offset : Nat} {byte : Byte} (observed : region.bytes.get? offset = some byte) :
    loaded.initialState.machine.memory.cellAt? region.allocId offset = some (byte, true) :=
  InitializedRegion.cellAt?_of_lookups (loaded.imagePresent region member).1
    (loaded.imagePresent region member).2 observed

/-- The initial entry address has not been silently truncated modulo 2^64. -/
theorem LoadedImage.entryRip_exact {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    loaded.initialState.rip.toNat = (preferredBase image).toNat + image.plan.layout.entryPointRva := by
  have h := loaded.entry
  change _ < 2 ^ 47 ∧ _ at h
  simp only [LoadedImage.initialState, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

/-- Each assigned base is the untruncated sum of the preferred base and its
actual region RVA; the complete region is inside the checked image extent. -/
theorem LoadedImage.regionPlacement_exact {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {assigned : InitializedRegion}
    (member : assigned ∈ assignedRegions image inputs loaded.patches) :
    ∃ region ∈ imageRegions image.plan loaded.patches,
      assigned.base.toNat = (preferredBase image).toNat + region.rva ∧
      assigned.bytes = region.bytes ∧
      assigned.base.toNat + assigned.bytes.length ≤
        (preferredBase image).toNat + image.plan.layout.sizeOfImage := by
  obtain ⟨⟨region, identity⟩, paired, rfl⟩ := List.mem_map.mp member
  have regionMember := (List.of_mem_zip paired).1
  have bound := imageRegions_bounded image.plan loaded.patches regionMember
  have imageBound := loaded.entry.1
  have exactBase : (BitVec.ofNat 64 ((preferredBase image).toNat + region.rva)).toNat =
      (preferredBase image).toNat + region.rva := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  exact ⟨region, regionMember, exactBase, rfl, by simp only [exactBase]; omega⟩

/-- The supplied file bytes independently parse as the checked writer's image. -/
theorem ImageInput.read_exact (image : ImageInput) :
    PE.readImage (Vec.ofHostBytes image.bytes) = .done image.plan.expectedImage Vec.empty := by
  rw [image.bytesExact, Vec.ofHostBytes_toHostBytes]
  exact PE.readImage_writeImage image.plan

end Grass.Platform.Win32.Loader
