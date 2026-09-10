import Grass.Memory.InitializedRegion

/-! Checked installation and placement laws shared by executable-image loaders. -/
namespace Grass.Memory.ImageInstall

open Grass.Core Grass.Memory

structure RegionIdentity where
  allocation : AllocId
  storage : StorageId
  epoch : EpochId
deriving DecidableEq, Repr

def installRegions? (before : MemoryState) : List InitializedRegion → Option MemoryState
  | [] => some before
  | region :: tail => do
      let next ← installInitializedRegion? before region
      installRegions? next tail

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

def RegionsPresent (memory : MemoryState) (regions : List InitializedRegion) : Prop :=
  ∀ region ∈ regions,
    memory.allocations.lookup region.allocId = some region.allocationRecord ∧
    memory.backings.lookup region.storageId = some region.backingRecord

instance (memory : MemoryState) (regions : List InitializedRegion) :
    Decidable (RegionsPresent memory regions) := by
  unfold RegionsPresent
  infer_instance

def CpuPlacementValid (record : AllocationRecord) : Prop :=
  record.live = true → record.space = .cpuVirtual →
    match record.base with
    | none => False
    | some base => FitsAllocation base record.extent.stop

instance (record : AllocationRecord) : Decidable (CpuPlacementValid record) := by
  unfold CpuPlacementValid
  split <;> infer_instance

@[simp] theorem cpuPlacementValid_initialized (region : InitializedRegion) :
    CpuPlacementValid region.allocationRecord ↔
      FitsAllocation region.base region.bytes.length := by
  simp [CpuPlacementValid, InitializedRegion.allocationRecord]

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

def PlacementValid (memory : MemoryState) : Prop :=
  memory.DedicatedBackings ∧
  (∀ entry ∈ memory.allocations.entries, CpuPlacementValid entry.2) ∧
  (∀ a ∈ memory.allocations.entries, ∀ b ∈ memory.allocations.entries,
    CpuPlacementsDisjoint a b)

instance (memory : MemoryState) : Decidable (PlacementValid memory) := by
  unfold PlacementValid
  infer_instance

def HistoryFresh (machine : MachineState) (regions : List InitializedRegion) : Prop :=
  ∀ region ∈ regions,
    (∀ event ∈ machine.events,
      event.event.provenance.root ≠ region.allocId ∧ event.event.mapping.backing ≠ region.storageId) ∧
    (∀ violation ∈ machine.violations.records?, violation.provenance.root ≠ region.allocId)

instance (machine : MachineState) (regions : List InitializedRegion) :
    Decidable (HistoryFresh machine regions) := by
  unfold HistoryFresh
  infer_instance

end Grass.Memory.ImageInstall
