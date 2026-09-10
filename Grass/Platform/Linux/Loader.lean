import Grass.Artifact.ELF.LoadPlan
import Grass.Memory.ImageInstall
import Grass.ISA.AArch64.Control

/-! Deterministic ELF segment installation into the shared virtual memory model.
This is a fixed-address native AArch64 image initialization component, not
execve, an initial Linux stack/auxv producer, a reached execution proof or a
physical page mapping. All existing machine ledgers and CPU inputs are retained;
only installed image memory and the image-derived initial PC change.
-/

namespace Grass.Platform.Linux.Loader
open Grass.Core Grass.Memory Grass.Memory.ImageInstall Grass.Std.Logical
open Grass.Artifact.ELF Grass.ISA.AArch64

/-- Explicit supplied machine/context/registers and fresh identity choices.
ISA feature and exception configuration remains a separate consumer obligation. -/
structure Inputs where
  environment : MachineState
  context : ContextId
  identities : List RegionIdentity
  cpu : Cpu

def regionFor (bytes : Std.Logical.ByteArray) (context : ContextId)
    (segment : ProgramHeader64) (identity : RegionIdentity) : InitializedRegion :=
  { allocId := identity.allocation, storageId := identity.storage, epoch := identity.epoch
    base := segment.virtualAddress, permission := segmentPermission segment.flags
    source := .imageMapping, owner := context, bytes := segmentBytes bytes segment }

def assignedRegions {profile : LoadProfile} {bytes : Std.Logical.ByteArray}
    (plan : LoadPlan profile bytes) (inputs : Inputs) : List InitializedRegion :=
  ((loadSegments plan.image).zip inputs.identities).map (fun (segment, identity) =>
    regionFor bytes inputs.context segment identity)

/-- Selected architecture and a four-byte aligned complete initial fetch range.
This checks geometry only; it does not fetch, decode or grant instruction access. -/
def EntryValid {profile : LoadProfile} {bytes : Std.Logical.ByteArray}
    (plan : LoadPlan profile bytes) (inputs : Inputs) : Prop :=
  profile.machine = 183 ∧
  inputs.environment.contexts.lookup inputs.context = some .thread ∧
  plan.image.header.entry.toNat % 4 = 0 ∧
  ∃ segment ∈ loadSegments plan.image,
    (segmentPermission segment.flags).execute = true ∧
    segment.virtualAddress.toNat ≤ plan.image.header.entry.toNat ∧
    plan.image.header.entry.toNat + 4 ≤ segment.virtualAddress.toNat + segment.memorySize.toNat
instance {profile : LoadProfile} {bytes : Std.Logical.ByteArray}
    (plan : LoadPlan profile bytes) (inputs : Inputs) : Decidable (EntryValid plan inputs) := by
  unfold EntryValid; infer_instance

/-- Receipt of the same parser/checker and actual shared installation algorithm. -/
structure LoadedImage (profile : LoadProfile) (bytes : Std.Logical.ByteArray) (inputs : Inputs) where
  plan : LoadPlan profile bytes
  identitiesComplete : inputs.identities.length = (loadSegments plan.image).length
  historyFresh : HistoryFresh inputs.environment (assignedRegions plan inputs)
  memory : MemoryState
  installed : installRegions? inputs.environment.memory (assignedRegions plan inputs) = some memory
  present : RegionsPresent memory (assignedRegions plan inputs)
  placement : PlacementValid memory
  entry : EntryValid plan inputs

def load? (profile : LoadProfile) (bytes : Std.Logical.ByteArray) (inputs : Inputs) :
    Option (LoadedImage profile bytes inputs) := do
  let plan ← plan? profile bytes
  if hi : inputs.identities.length = (loadSegments plan.image).length then
  if hh : HistoryFresh inputs.environment (assignedRegions plan inputs) then
    match hm : installRegions? inputs.environment.memory (assignedRegions plan inputs) with
    | none => none
    | some memory =>
      if hp : RegionsPresent memory (assignedRegions plan inputs) then
      if hl : PlacementValid memory then
      if he : EntryValid plan inputs then
        some ⟨plan, hi, hh, memory, hm, hp, hl, he⟩
      else none else none else none
  else none else none

def LoadedImage.machine {profile bytes inputs} (loaded : LoadedImage profile bytes inputs) :
    MachineState := { inputs.environment with memory := loaded.memory }

def LoadedImage.cpu {profile bytes inputs} (loaded : LoadedImage profile bytes inputs) : Cpu :=
  { inputs.cpu with pc := loaded.plan.image.header.entry }

def LoadedImage.context {profile bytes inputs} (_ : LoadedImage profile bytes inputs) : ContextId :=
  inputs.context

theorem LoadedImage.environment_frame {profile bytes inputs} (loaded : LoadedImage profile bytes inputs) :
    { loaded.machine with memory := inputs.environment.memory } = inputs.environment := rfl

theorem LoadedImage.registers_exact {profile bytes inputs} (loaded : LoadedImage profile bytes inputs) :
    loaded.cpu.gpr = inputs.cpu.gpr ∧ loaded.cpu.nzcv = inputs.cpu.nzcv := ⟨rfl, rfl⟩

theorem LoadedImage.entry_exact {profile bytes inputs} (loaded : LoadedImage profile bytes inputs) :
    loaded.cpu.pc = loaded.plan.image.header.entry := rfl

/-- The image-derived PC names a complete aligned word in an actually installed
executable allocation, without manufacturing a fetch or access grant. -/
theorem LoadedImage.entry_region {profile bytes inputs} (loaded : LoadedImage profile bytes inputs) :
    ∃ region ∈ assignedRegions loaded.plan inputs,
      loaded.machine.memory.allocations.lookup region.allocId = some region.allocationRecord ∧
      region.permission.execute = true ∧ region.base.toNat ≤ loaded.cpu.pc.toNat ∧
      loaded.cpu.pc.toNat + 4 ≤ region.base.toNat + region.bytes.length := by
  obtain ⟨segment, member, executable, lower, upper⟩ := loaded.entry.2.2.2
  have complete := loaded.identitiesComplete
  have zipped : segment ∈ ((loadSegments loaded.plan.image).zip inputs.identities).map Prod.fst := by
    rw [List.map_fst_zip (by omega)]
    exact member
  obtain ⟨⟨selected, identity⟩, paired, equal⟩ := List.mem_map.mp zipped
  dsimp at equal
  subst selected
  have assigned : regionFor bytes inputs.context segment identity ∈ assignedRegions loaded.plan inputs :=
    List.mem_map.mpr ⟨(segment, identity), paired, rfl⟩
  refine ⟨regionFor bytes inputs.context segment identity, assigned,
    (loaded.present _ assigned).1, executable, lower, ?_⟩
  change loaded.plan.image.header.entry.toNat + 4 ≤
    segment.virtualAddress.toNat + (segmentBytes bytes segment).length
  rw [segmentBytes_length (loaded.plan.segment_valid member)]
  exact upper

/-- Every installed logical segment byte is initialized in authoritative storage. -/
theorem LoadedImage.cellAt? {profile bytes inputs} (loaded : LoadedImage profile bytes inputs)
    {region : InitializedRegion} (member : region ∈ assignedRegions loaded.plan inputs)
    {offset : Nat} {byte : Byte} (observed : region.bytes.get? offset = some byte) :
    loaded.machine.memory.cellAt? region.allocId offset = some (byte, true) :=
  InitializedRegion.cellAt?_of_lookups (loaded.present region member).1
    (loaded.present region member).2 observed

/-- Exact parsed file bytes reach the backing of the corresponding assigned segment. -/
theorem LoadedImage.file_byte {profile bytes inputs} (loaded : LoadedImage profile bytes inputs)
    {segment : ProgramHeader64} {identity : RegionIdentity}
    (paired : (segment, identity) ∈ (loadSegments loaded.plan.image).zip inputs.identities)
    {offset : Nat} {byte : Byte} (inside : offset < segment.fileSize.toNat)
    (source : bytes.get? (segment.offset.toNat + offset) = some byte) :
    loaded.machine.memory.cellAt? identity.allocation offset = some (byte, true) := by
  have valid := loaded.plan.segment_valid (List.of_mem_zip paired).1
  apply loaded.cellAt? (region := regionFor bytes inputs.context segment identity)
  · exact List.mem_map.mpr ⟨(segment, identity), paired, rfl⟩
  · exact (segmentBytes_file inside valid.2.1).trans source

/-- The segment's zero-fill tail is actually installed, not merely sized. -/
theorem LoadedImage.zero_byte {profile bytes inputs} (loaded : LoadedImage profile bytes inputs)
    {segment : ProgramHeader64} {identity : RegionIdentity}
    (paired : (segment, identity) ∈ (loadSegments loaded.plan.image).zip inputs.identities)
    {offset : Nat} (tail : segment.fileSize.toNat ≤ offset) (inside : offset < segment.memorySize.toNat) :
    loaded.machine.memory.cellAt? identity.allocation offset = some (0, true) := by
  have valid := loaded.plan.segment_valid (List.of_mem_zip paired).1
  apply loaded.cellAt? (region := regionFor bytes inputs.context segment identity)
  · exact List.mem_map.mpr ⟨(segment, identity), paired, rfl⟩
  · exact segmentBytes_zero valid.2.1 tail inside

end Grass.Platform.Linux.Loader
