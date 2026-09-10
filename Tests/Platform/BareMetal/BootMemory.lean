import Grass.Platform.BareMetal.BootMemory

/-!
# Bare-metal boot-memory admission controls

These examples construct every candidate through `installBacking?` and
`allocate?`.  They test the model checker against a supplied physical map; they
do not claim that the map describes any particular machine.
-/

namespace Tests.Platform.BareMetal.BootMemory

open Grass.Core Grass.Memory Grass.Std.Logical
open Grass.Platform.BareMetal.BootMemory

private def allocs : FreshSupply AllocTag := .initial
private def stores : FreshSupply StorageTag := .initial
private def epochs : FreshSupply EpochTag := .initial
private def contexts : FreshSupply ContextTag := .initial

private def image : AllocId := allocs.fresh.1
private def alias : AllocId := allocs.fresh.2.fresh.1
private def imageStore : StorageId := stores.fresh.1
private def aliasStore : StorageId := stores.fresh.2.fresh.1
private def epoch : EpochId := epochs.fresh.1
private def core : ContextId := contexts.fresh.1
private def other : ContextId := contexts.fresh.2.fresh.1

private def backing : BackingRecord := { capacity := 16, bytes := .empty }

/-- The represented object starts at local offset four.  Its physical placement
is consequently `[0x1004, 0x1008)`, rather than beginning at the allocation
base. -/
private def imageRecord : AllocationRecord :=
  { extent := ⟨4, 4⟩
    epoch := epoch
    space := .cpuPhysical
    source := .imageMapping
    owners := [core]
    permission := .readExecute
    live := true
    backing := imageStore
    origin := 0
    base := some 0x1000 }

private def physicalMap : PhysicalMap :=
  { ram := [⟨0x1000, 0x100⟩]
    devices := [⟨0x2000, 0x100⟩] }

private def imageMemory? : Option MemoryState := do
  let installed ← MemoryState.empty.installBacking? imageStore backing
  installed.allocate? image imageRecord

private def imageMemory : MemoryState := imageMemory?.getD .empty
private def before : MachineState := MachineState.initial imageMemory

theorem image_enters_through_public_doors : imageMemory?.isSome := by decide

theorem machine_initial_produces_a_fresh_candidate : Fresh before := by decide

theorem nonzero_local_start_is_part_of_physical_placement :
    allocationPlacement imageRecord 0x1000 = ⟨0x1004, 4⟩ := by decide

theorem represented_image_is_admitted :
    (admit? physicalMap core before).isSome := by decide

private def admission : Admission physicalMap core before :=
  (admit? physicalMap core before).get represented_image_is_admitted

/-- Admission exposes the checks on the record found in the exact supplied
state, rather than reconstructing a second placement witness in the fixture. -/
theorem admitted_image_has_the_checked_contract :
    LiveAllocationAdmissible physicalMap core imageRecord := by
  apply admission.liveAllocation (id := image)
  · decide
  · rfl

theorem admission_preserves_the_exact_input_memory :
    admission.machine.memory = imageMemory :=
  admission.machine_memory

theorem admitted_input_has_no_outstanding_grants :
    imageMemory.grantEntries = [] :=
  admission.no_grants

theorem admission_starts_with_fresh_model_history :
    admission.machine.obligations = .empty ∧
      admission.machine.violations = .empty ∧
      admission.machine.events = [] ∧
      admission.machine.eventSupply = .initial ∧
      admission.machine.faults = [] ∧
      admission.machine.synchronization = .empty :=
  admission.machine_is_fresh

private def insufficientRam : PhysicalMap :=
  { physicalMap with ram := [⟨0x1000, 7⟩] }

private def overlappingDevice : PhysicalMap :=
  { physicalMap with devices := [⟨0x1006, 1⟩] }

theorem ram_must_cover_the_complete_placed_extent :
    admit? insufficientRam core before = none := by decide

theorem a_device_window_excludes_overlapping_ram_bytes :
    admit? overlappingDevice core before = none := by decide

/-! Distinct abstract backings do not establish distinct numeric placements. -/

private def aliasRecord : AllocationRecord :=
  { imageRecord with backing := aliasStore }

private def aliasedMemory? : Option MemoryState := do
  let state ← MemoryState.empty.installBacking? imageStore backing
  let state ← state.installBacking? aliasStore backing
  let state ← state.allocate? image imageRecord
  state.allocate? alias aliasRecord

private def aliasedMemory : MemoryState := aliasedMemory?.getD .empty

theorem public_doors_allow_distinct_backings_at_the_same_numeric_placement :
    aliasedMemory?.isSome ∧ aliasedMemory.DedicatedBackings := by decide

theorem boot_admission_rejects_the_numeric_alias :
    admit? physicalMap core (MachineState.initial aliasedMemory) = none := by decide

/-! Each remaining candidate is independently constructed by the same public
doors, so the negative checks do not depend on an unsealed `MemoryState`. -/

private def oneRecordMemory? (record : AllocationRecord) : Option MemoryState := do
  let installed ← MemoryState.empty.installBacking? imageStore backing
  installed.allocate? image record

private def oneRecordMemory (record : AllocationRecord) : MemoryState :=
  (oneRecordMemory? record).getD .empty

private def oneRecordBefore (record : AllocationRecord) : MachineState :=
  MachineState.initial (oneRecordMemory record)

private def wrappedRecord : AllocationRecord :=
  { imageRecord with base := some 0xffffffffffffffff }

private def unplacedRecord : AllocationRecord :=
  { imageRecord with base := none }

private def wrongSpaceRecord : AllocationRecord :=
  { imageRecord with space := .cpuVirtual }

private def deviceSourceRecord : AllocationRecord :=
  { imageRecord with source := .deviceMemory }

private def wrongOwnerRecord : AllocationRecord :=
  { imageRecord with owners := [other] }

theorem malformed_boot_candidates_still_enter_through_memory_doors :
    (oneRecordMemory? wrappedRecord).isSome ∧
      (oneRecordMemory? unplacedRecord).isSome ∧
      (oneRecordMemory? wrongSpaceRecord).isSome ∧
      (oneRecordMemory? deviceSourceRecord).isSome ∧
      (oneRecordMemory? wrongOwnerRecord).isSome := by decide

theorem boot_admission_rejects_wrap_unplaced_wrong_space_device_and_owner :
    admit? physicalMap core (oneRecordBefore wrappedRecord) = none ∧
      admit? physicalMap core (oneRecordBefore unplacedRecord) = none ∧
      admit? physicalMap core (oneRecordBefore wrongSpaceRecord) = none ∧
      admit? physicalMap core (oneRecordBefore deviceSourceRecord) = none ∧
      admit? physicalMap core (oneRecordBefore wrongOwnerRecord) = none := by decide

/-- A prior context is enough to make the supplied machine nonfresh. Admission
does not erase it and pretend that the snapshot was initial. -/
private def machineWithHistory : MachineState := before.noteContext other .thread

theorem boot_admission_rejects_a_nonfresh_machine_snapshot :
    admit? physicalMap core machineWithHistory = none := by decide

end Tests.Platform.BareMetal.BootMemory
