import Grass.Memory.State

/-!
# Bare-metal boot memory admission

This module validates an already constructed `MachineState` against a supplied
numeric physical-memory description.  The description lists ordinary RAM and
device-reserved windows; it describes the candidate model, not a
claim that the list is a complete or hardware-verified physical inventory.

Admission does not install allocations, alter bytes, or discard machine history.
The supplied snapshot must be fresh. Every represented live
allocation must be placed in `cpu.physical`, avoid address wrap and device
windows, lie inside one declared RAM window, belong solely to the boot CPU
context, and have no outstanding grants.  The backing and cross-allocation
requirements remain the memory layer's `MemoryState.DedicatedBackings` plus the
separate numeric-placement check below.
-/

namespace Grass.Platform.BareMetal.BootMemory

open Grass.Core Grass.Memory Grass.Std.Logical

/-- Nominal source for RAM made available directly by the bare-metal boot
environment, rather than by an image mapping or a stack allocator. -/
def bootRamSource : AllocationSourceId := ⟨⟨"bareMetal.bootRam"⟩⟩

/-- The fixed set of allocation sources that may describe ordinary boot RAM. -/
def BootRAMSource (source : AllocationSourceId) : Prop :=
  source = .imageMapping ∨ source = .stack ∨ source = bootRamSource

instance (source : AllocationSourceId) : Decidable (BootRAMSource source) :=
  if image : source = .imageMapping then .isTrue (.inl image)
  else if stack : source = .stack then .isTrue (.inr (.inl stack))
  else if boot : source = bootRamSource then .isTrue (.inr (.inr boot))
  else .isFalse (fun admitted => admitted.elim image (fun rest => rest.elim stack boot))

/-- A named physical-coordinate window beginning at a 64-bit machine address. -/
structure PhysicalWindow where
  base : MachineAddress
  size : Nat
deriving DecidableEq, Repr

namespace PhysicalWindow

/-- The window represented as a natural-number range for shared range arithmetic. -/
def numericRange (window : PhysicalWindow) : ByteRange :=
  ⟨window.base.toNat, window.size⟩

/-- A physical window is well formed when its final byte does not exceed the
64-bit numeric address domain. -/
def WellFormed (window : PhysicalWindow) : Prop :=
  window.numericRange.WithinBound (2 ^ 64)

instance (window : PhysicalWindow) : Decidable window.WellFormed :=
  inferInstanceAs (Decidable (window.numericRange.WithinBound (2 ^ 64)))

/-- `wellFormed_iff_fitsAllocation` connects the physical wrapper to the shared
non-wrapping address arithmetic. -/
theorem wellFormed_iff_fitsAllocation (window : PhysicalWindow) :
    window.WellFormed ↔ FitsAllocation window.base window.size := by
  rfl

end PhysicalWindow

/-- The RAM windows offered to the candidate state and the physical windows
reserved for devices.  `PhysicalMap.WellFormed` validates each numeric extent;
the map itself grants no allocation authority. -/
structure PhysicalMap where
  ram : List PhysicalWindow
  devices : List PhysicalWindow
deriving DecidableEq, Repr

namespace PhysicalMap

/-- Every supplied RAM and device window stays inside the 64-bit physical domain. -/
def WellFormed (map : PhysicalMap) : Prop :=
  (∀ window ∈ map.ram, window.WellFormed) ∧
    ∀ window ∈ map.devices, window.WellFormed

instance (map : PhysicalMap) : Decidable map.WellFormed := by
  unfold WellFormed
  infer_instance

end PhysicalMap

/-- The numeric physical bytes occupied by `record` at `base`.  The allocation
extent may begin at a nonzero offset, so placement shifts the complete extent. -/
def allocationPlacement (record : AllocationRecord) (base : MachineAddress) : ByteRange :=
  record.extent.shift base.toNat

/-- The placement bound is exactly the memory layer's whole-allocation wrap check. -/
theorem allocationPlacement_withinBound_iff (record : AllocationRecord)
    (base : MachineAddress) :
    (allocationPlacement record base).WithinBound (2 ^ 64) ↔
      FitsAllocation base record.extent.stop := by
  simp only [allocationPlacement, ByteRange.withinBound_def, ByteRange.shift,
    ByteRange.stop, FitsAllocation]
  omega

/-- Admission conditions for one live allocation after its concrete base has
been recovered from the record. -/
def LiveAllocationAdmissible (map : PhysicalMap) (context : ContextId)
    (record : AllocationRecord) : Prop :=
  record.space = AddressSpaceId.cpuPhysical ∧
    BootRAMSource record.source ∧
    record.owners = [context] ∧
    match record.base with
    | none => False
    | some base =>
        FitsAllocation base record.extent.stop ∧
        (∃ ram ∈ map.ram,
          ram.numericRange.Contains (allocationPlacement record base)) ∧
        (∀ device ∈ map.devices,
          (allocationPlacement record base).Disjoint device.numericRange)

instance (map : PhysicalMap) (context : ContextId) (record : AllocationRecord) :
    Decidable (LiveAllocationAdmissible map context record) := by
  unfold LiveAllocationAdmissible
  split <;> infer_instance

/-- Every represented live allocation satisfies `LiveAllocationAdmissible`;
dead historical records impose no physical-placement requirement. -/
def AllLiveAllocationsAdmissible (map : PhysicalMap) (context : ContextId)
    (memory : MemoryState) : Prop :=
  ∀ entry ∈ memory.allocations.entries,
    entry.2.live = true → LiveAllocationAdmissible map context entry.2

instance (map : PhysicalMap) (context : ContextId) (memory : MemoryState) :
    Decidable (AllLiveAllocationsAdmissible map context memory) := by
  unfold AllLiveAllocationsAdmissible
  infer_instance

/-- A pair of represented allocations is physically separated whenever both
records are live.  Bases are read from the records rather than supplied anew. -/
def LivePlacementPair (left right : AllocId × AllocationRecord) : Prop :=
  left.2.live = false ∨ right.2.live = false ∨
    match left.2.base, right.2.base with
    | some leftBase, some rightBase =>
        (allocationPlacement left.2 leftBase).Disjoint
          (allocationPlacement right.2 rightBase)
    | _, _ => False

instance (left right : AllocId × AllocationRecord) :
    Decidable (LivePlacementPair left right) := by
  unfold LivePlacementPair
  split <;> infer_instance

/-- All represented live allocations occupy pairwise disjoint numeric physical
ranges.  This is independent of abstract backing identity. -/
def LivePlacementsDisjoint (memory : MemoryState) : Prop :=
  memory.allocations.entries.Pairwise LivePlacementPair

instance (memory : MemoryState) : Decidable (LivePlacementsDisjoint memory) := by
  unfold LivePlacementsDisjoint
  infer_instance

/-- The complete memory predicate, factored so callers can inspect the exact
storage requirements independently of machine-history freshness. -/
def MemoryAdmissible (map : PhysicalMap) (context : ContextId)
    (memory : MemoryState) : Prop :=
  map.WellFormed ∧
    memory.DedicatedBackings ∧
    memory.grantEntries = [] ∧
    AllLiveAllocationsAdmissible map context memory ∧
    LivePlacementsDisjoint memory

instance (map : PhysicalMap) (context : ContextId) (memory : MemoryState) :
    Decidable (MemoryAdmissible map context memory) := by
  unfold MemoryAdmissible
  infer_instance

/-- A boot snapshot is fresh when it carries no prior obligations, findings,
events, contexts, faults, or synchronization history and uses the initial event
supply. -/
def Fresh (before : MachineState) : Prop :=
  before.obligations.entries.isEmpty = true ∧
    before.violations = .empty ∧
    before.events.isEmpty = true ∧
    before.eventSupply.fresh.1 =
      (FreshSupply.initial (Tag := EventTag)).fresh.1 ∧
    before.faults.isEmpty = true ∧
    before.contexts.entries.isEmpty = true ∧
    before.synchronization = .empty

instance (before : MachineState) : Decidable (Fresh before) := by
  unfold Fresh
  infer_instance

/-- The public next-identity observation used by `Fresh` is equivalent to the
event supply itself being initial. -/
theorem eventSupply_fresh_eq_iff (supply : FreshSupply EventTag) :
    supply.fresh.1 = (FreshSupply.initial (Tag := EventTag)).fresh.1 ↔
      supply = .initial := by
  cases supply
  simp [FreshSupply.fresh, FreshSupply.initial]

/-- The complete predicate decided by `admit?`. It validates the exact supplied
machine snapshot without constructing replacement storage or erasing history. -/
def Admissible (map : PhysicalMap) (context : ContextId)
    (before : MachineState) : Prop :=
  Fresh before ∧ MemoryAdmissible map context before.memory

instance (map : PhysicalMap) (context : ContextId) (before : MachineState) :
    Decidable (Admissible map context before) := by
  unfold Admissible
  infer_instance

/-- Dependent evidence that the supplied machine passed the boot admission rule. -/
structure Admission (map : PhysicalMap) (context : ContextId)
    (before : MachineState) : Type where
  admissible : Admissible map context before

/-- Check a supplied machine and return evidence indexed by that exact snapshot. -/
def admit? (map : PhysicalMap) (context : ContextId) (before : MachineState) :
    Option (Admission map context before) :=
  if h : Admissible map context before then some ⟨h⟩ else none

/-- `admit?_isSome` states the exact acceptance rule of the boot-memory checker. -/
theorem admit?_isSome (map : PhysicalMap) (context : ContextId) (before : MachineState) :
    (admit? map context before).isSome ↔ Admissible map context before := by
  by_cases h : Admissible map context before <;> simp [admit?, h]

/-- `admit?_eq_none` states that refusal is precisely failure of `Admissible`. -/
theorem admit?_eq_none (map : PhysicalMap) (context : ContextId) (before : MachineState) :
    admit? map context before = none ↔ ¬ Admissible map context before := by
  by_cases h : Admissible map context before <;> simp [admit?, h]

namespace Admission

private theorem finiteMap_eq_empty_of_entries_eq_nil {K V : Type}
    {map : FiniteMap K V} (empty : map.entries = []) : map = .empty := by
  cases map
  simp_all [FiniteMap.empty]

/-- `Admission.machine` preserves the supplied snapshot and records the sole
boot CPU context as an ordinary thread. -/
def machine {map : PhysicalMap} {context : ContextId} {before : MachineState}
    (_admission : Admission map context before) : MachineState :=
  before.noteContext context .thread

/-- `machine_eq_noteContext` states the complete snapshot transformation. -/
@[simp] theorem machine_eq_noteContext {map : PhysicalMap} {context : ContextId}
    {before : MachineState} (admission : Admission map context before) :
    admission.machine = before.noteContext context .thread := rfl

/-- `machine_memory` proves boot admission performs no memory or byte mutation. -/
@[simp] theorem machine_memory {map : PhysicalMap} {context : ContextId}
    {before : MachineState} (admission : Admission map context before) :
    admission.machine.memory = before.memory := rfl

/-- `machine_context` proves the admitted machine records the boot CPU thread. -/
@[simp] theorem machine_context {map : PhysicalMap} {context : ContextId}
    {before : MachineState} (admission : Admission map context before) :
    admission.machine.contexts.lookup context = some .thread := by
  simp [machine, MachineState.noteContext]

/-- `machine_is_fresh` exposes the empty ledgers and traces required from the
supplied fresh snapshot and preserved by `Admission.machine`. -/
theorem machine_is_fresh {map : PhysicalMap} {context : ContextId}
    {before : MachineState} (admission : Admission map context before) :
    admission.machine.obligations = .empty ∧
      admission.machine.violations = .empty ∧
      admission.machine.events = [] ∧
      admission.machine.eventSupply = .initial ∧
      admission.machine.faults = [] ∧
      admission.machine.synchronization = .empty := by
  have obligations : before.obligations.entries = [] := by
    simpa using admission.admissible.1.1
  have events : before.events = [] := by
    simpa using admission.admissible.1.2.2.1
  have faults : before.faults = [] := by
    simpa using admission.admissible.1.2.2.2.2.1
  exact ⟨finiteMap_eq_empty_of_entries_eq_nil obligations,
    admission.admissible.1.2.1, events,
    (eventSupply_fresh_eq_iff before.eventSupply).1
      admission.admissible.1.2.2.2.1,
    faults, admission.admissible.1.2.2.2.2.2.2⟩

/-- `no_grants` exposes sole ownership's absence of leftover authority grants. -/
theorem no_grants {map : PhysicalMap} {context : ContextId}
    {before : MachineState} (admission : Admission map context before) :
    before.memory.grantEntries = [] :=
  admission.admissible.2.2.2.1

/-- `liveAllocation` projects all physical and ownership checks for an actual
live allocation lookup. -/
theorem liveAllocation {map : PhysicalMap} {context : ContextId}
    {before : MachineState} (admission : Admission map context before)
    {id : AllocId} {record : AllocationRecord}
    (lookup : before.memory.allocations.lookup id = some record)
    (live : record.live = true) : LiveAllocationAdmissible map context record := by
  exact admission.admissible.2.2.2.2.1 (id, record)
    (FiniteMap.mem_of_lookup lookup) live

end Admission

/-- Evidence that one nonempty initialized range is a readable executable entry
inside an admitted live allocation. -/
structure Entry {map : PhysicalMap} {context : ContextId} {before : MachineState}
    (admission : Admission map context before) (id : AllocId) (range : ByteRange) : Type where
  record : AllocationRecord
  lookup : before.memory.allocations.lookup id = some record
  live : record.live = true
  base : MachineAddress
  baseExact : record.base = some base
  contained : record.extent.Contains range
  nonempty : ¬ range.IsEmpty
  initialized : before.memory.RangeInitialized id range
  readExecute : record.permission.Grants Permission.readExecute

/-- Check an admitted memory range as an initialized readable executable entry. -/
def entry? {map : PhysicalMap} {context : ContextId} {before : MachineState}
    (admission : Admission map context before) (id : AllocId) (range : ByteRange) :
    Option (Entry admission id range) :=
  match lookup : before.memory.allocations.lookup id with
  | none => none
  | some record =>
      if live : record.live = true then
        match baseExact : record.base with
        | none => none
        | some base =>
            if contained : record.extent.Contains range then
              if nonempty : ¬ range.IsEmpty then
                if initialized : before.memory.RangeInitialized id range then
                  if executable : record.permission.Grants Permission.readExecute then
                    some ⟨record, lookup, live, base, baseExact, contained, nonempty,
                      initialized, executable⟩
                  else none
                else none
              else none
            else none
      else none

namespace Entry

/-- The exact root provenance selected by an admitted entry. -/
def provenance {map : PhysicalMap} {context : ContextId} {before : MachineState}
    {admission : Admission map context before} {id : AllocId} {range : ByteRange}
    (entry : Entry admission id range) : Provenance where
  space := entry.record.space
  root := id
  epoch := entry.record.epoch
  source := entry.record.source
  rootExtent := entry.record.extent
  path := []

/-- The numeric program-counter address at the first byte of the selected range. -/
def pc {map : PhysicalMap} {context : ContextId} {before : MachineState}
    {admission : Admission map context before} {id : AllocId} {range : ByteRange}
    (entry : Entry admission id range) : MachineAddress :=
  addressOf entry.base range.start

/-- `addressAt?_eq_pc` proves the selected PC comes from the admitted allocation's
actual placement rather than an independently supplied address. -/
theorem addressAt?_eq_pc {map : PhysicalMap} {context : ContextId}
    {before : MachineState} {admission : Admission map context before}
    {id : AllocId} {range : ByteRange} (entry : Entry admission id range) :
    before.memory.addressAt? id range.start = some entry.pc := by
  simp [MemoryState.addressAt?, entry.lookup, entry.baseExact, pc]

/-- `space_cpuPhysical` ties the selected entry to the admitted physical space. -/
theorem space_cpuPhysical {map : PhysicalMap} {context : ContextId}
    {before : MachineState} {admission : Admission map context before}
    {id : AllocId} {range : ByteRange} (entry : Entry admission id range) :
    entry.provenance.space = AddressSpaceId.cpuPhysical := by
  exact (admission.liveAllocation entry.lookup entry.live).1

end Entry

end Grass.Platform.BareMetal.BootMemory
