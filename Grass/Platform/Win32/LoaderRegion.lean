import Grass.Memory.State
import Grass.Std.Logical.Vec

/-! Deterministic installation of one initialized loader region. This is memory
bookkeeping only: it does not claim Windows loader adequacy or memory safety. -/

namespace Grass.Platform.Win32

open Grass.Std.Logical

/-- Neutral description of one fully initialized allocated region. -/
structure InitializedRegion where
  allocId : Grass.Memory.AllocId
  storageId : Grass.Memory.StorageId
  epoch : Grass.Memory.EpochId
  base : Grass.Memory.MachineAddress
  permission : Grass.Memory.Permission
  source : Grass.Memory.AllocationSourceId
  owner : Grass.Core.ContextId
  bytes : Vec Byte
deriving DecidableEq, Repr

def InitializedRegion.backingRecord (region : InitializedRegion) : Grass.Memory.BackingRecord :=
  { capacity := region.bytes.length
    bytes := Grass.Memory.ByteStore.empty.write 0 region.bytes.toList true }

def InitializedRegion.allocationRecord (region : InitializedRegion) : Grass.Memory.AllocationRecord :=
  { extent := ⟨0, region.bytes.length⟩
    epoch := region.epoch
    space := Grass.Memory.AddressSpaceId.cpuVirtual
    source := region.source
    owners := [region.owner]
    permission := region.permission
    live := true
    backing := region.storageId
    origin := 0
    base := some region.base }

/-- Freshness checked against the allocation, backing, and outstanding-grant records
represented by one memory state. It does not claim a globally fresh identity. -/
def MemoryFresh (state : Grass.Memory.MemoryState) (region : InitializedRegion) : Prop :=
  state.allocations.lookup region.allocId = none ∧
  state.backings.lookup region.storageId = none ∧
  state.grantEntries.all (fun entry => decide (entry.2.provenance.root ≠ region.allocId)) = true ∧
  state.allocations.entries.all (fun entry => decide (entry.2.backing ≠ region.storageId)) = true

instance (state : Grass.Memory.MemoryState) (region : InitializedRegion) :
    Decidable (MemoryFresh state region) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Represented freshness excludes every outstanding grant rooted at this allocation ID. -/
theorem MemoryFresh.grant_root_ne {state : Grass.Memory.MemoryState}
    {region : InitializedRegion} (fresh : MemoryFresh state region)
    {entry : Grass.Memory.GrantId × Grass.Memory.AuthorityGrant}
    (member : entry ∈ state.grantEntries) : entry.2.provenance.root ≠ region.allocId := by
  exact of_decide_eq_true (List.all_eq_true.mp fresh.2.2.1 entry member)

/-- Represented freshness excludes every allocation-table reference to this storage ID. -/
theorem MemoryFresh.allocation_backing_ne {state : Grass.Memory.MemoryState}
    {region : InitializedRegion} (fresh : MemoryFresh state region)
    {entry : Grass.Memory.AllocId × Grass.Memory.AllocationRecord}
    (member : entry ∈ state.allocations.entries) : entry.2.backing ≠ region.storageId := by
  exact of_decide_eq_true (List.all_eq_true.mp fresh.2.2.2 entry member)

/-- Install a represented-state-fresh backing and its exact allocation view. The public
doors retain all collision and dedicated-backing refusal behavior. -/
def installInitializedRegion? (before : Grass.Memory.MemoryState) (region : InitializedRegion) :
    Option Grass.Memory.MemoryState :=
  if Grass.Memory.FitsAllocation region.base region.bytes.length ∧ MemoryFresh before region then
    do
      let withBacking ← before.installBacking? region.storageId region.backingRecord
      withBacking.allocate? region.allocId region.allocationRecord
  else none

/-- Success establishes the helper's spatial and represented-state freshness guards. -/
theorem installInitializedRegion?_admitted {before after : Grass.Memory.MemoryState}
    {region : InitializedRegion}
    (success : installInitializedRegion? before region = some after) :
    Grass.Memory.FitsAllocation region.base region.bytes.length ∧ MemoryFresh before region := by
  by_cases admitted : Grass.Memory.FitsAllocation region.base region.bytes.length ∧
      MemoryFresh before region
  · exact admitted
  · simp [installInitializedRegion?, admitted] at success

/-- A remaining grant rooted at the requested allocation ID refuses installation. -/
theorem installInitializedRegion?_eq_none_of_grant_root
    (before : Grass.Memory.MemoryState) (region : InitializedRegion)
    {entry : Grass.Memory.GrantId × Grass.Memory.AuthorityGrant}
    (member : entry ∈ before.grantEntries)
    (sameRoot : entry.2.provenance.root = region.allocId) :
    installInitializedRegion? before region = none := by
  have notFresh : ¬ MemoryFresh before region := fun fresh =>
    (MemoryFresh.grant_root_ne fresh member) sameRoot
  simp [installInitializedRegion?, notFresh]

/-- A remaining allocation-table reference to the requested storage ID refuses installation. -/
theorem installInitializedRegion?_eq_none_of_allocation_backing
    (before : Grass.Memory.MemoryState) (region : InitializedRegion)
    {entry : Grass.Memory.AllocId × Grass.Memory.AllocationRecord}
    (member : entry ∈ before.allocations.entries)
    (sameBacking : entry.2.backing = region.storageId) :
    installInitializedRegion? before region = none := by
  have notFresh : ¬ MemoryFresh before region := fun fresh =>
    (MemoryFresh.allocation_backing_ne fresh member) sameBacking
  simp [installInitializedRegion?, notFresh]

/-- A successful helper call records the exact allocation through `allocate?`. -/
theorem installInitializedRegion?_allocation {before after : Grass.Memory.MemoryState}
    {region : InitializedRegion}
    (success : installInitializedRegion? before region = some after) :
    after.allocations.lookup region.allocId = some region.allocationRecord := by
  have admitted := installInitializedRegion?_admitted success
  unfold installInitializedRegion? at success
  rw [if_pos admitted] at success
  change (before.installBacking? region.storageId region.backingRecord).bind
    (fun withBacking => withBacking.allocate? region.allocId region.allocationRecord) =
      some after at success
  rw [Option.bind_eq_some_iff] at success
  obtain ⟨withBacking, installed, allocated⟩ := success
  exact Grass.Memory.MemoryState.allocate?_lookup_self allocated

/-- Installation establishes represented-state freshness for its identities. -/
theorem installInitializedRegion?_fresh {before after : Grass.Memory.MemoryState}
    {region : InitializedRegion}
    (success : installInitializedRegion? before region = some after) :
    MemoryFresh before region :=
  (installInitializedRegion?_admitted success).2

/-- In particular, installation never replaces an existing allocation identity. -/
theorem installInitializedRegion?_allocation_absent {before after : Grass.Memory.MemoryState}
    {region : InitializedRegion}
    (success : installInitializedRegion? before region = some after) :
    before.allocations.lookup region.allocId = none :=
  (installInitializedRegion?_fresh success).1

/-- Allocation identities other than the requested fresh one retain their lookup. -/
theorem installInitializedRegion?_allocation_ne {before after : Grass.Memory.MemoryState}
    {region : InitializedRegion} {other : Grass.Memory.AllocId}
    (success : installInitializedRegion? before region = some after)
    (different : other ≠ region.allocId) :
    after.allocations.lookup other = before.allocations.lookup other := by
  have admitted := installInitializedRegion?_admitted success
  unfold installInitializedRegion? at success
  rw [if_pos admitted] at success
  change (before.installBacking? region.storageId region.backingRecord).bind
    (fun withBacking => withBacking.allocate? region.allocId region.allocationRecord) =
      some after at success
  rw [Option.bind_eq_some_iff] at success
  obtain ⟨withBacking, installed, allocated⟩ := success
  rw [Grass.Memory.MemoryState.allocate?_lookup_ne allocated different]
  rw [Grass.Memory.MemoryState.allocations_installBacking? installed]

/-- The backing installed for a successful region is the exact initialized record. -/
theorem installInitializedRegion?_backing {before after : Grass.Memory.MemoryState}
    {region : InitializedRegion}
    (success : installInitializedRegion? before region = some after) :
    after.backings.lookup region.storageId = some region.backingRecord := by
  have admitted := installInitializedRegion?_admitted success
  unfold installInitializedRegion? at success
  rw [if_pos admitted] at success
  change (before.installBacking? region.storageId region.backingRecord).bind
    (fun withBacking => withBacking.allocate? region.allocId region.allocationRecord) =
      some after at success
  rw [Option.bind_eq_some_iff] at success
  obtain ⟨withBacking, installed, allocated⟩ := success
  unfold Grass.Memory.MemoryState.installBacking? at installed
  cases hbacking : before.backings.lookup region.storageId with
  | some prior => simp [hbacking] at installed
  | none =>
    simp [hbacking] at installed
    subst withBacking
    unfold Grass.Memory.MemoryState.allocate? at allocated
    split at allocated
    · contradiction
    · injection allocated with result
      subst after
      exact Grass.Std.Logical.FiniteMap.lookup_insert_self _ _ _

/-- Backing identities other than the newly installed one retain their lookup. -/
theorem installInitializedRegion?_backing_ne {before after : Grass.Memory.MemoryState}
    {region : InitializedRegion} {other : Grass.Memory.StorageId}
    (success : installInitializedRegion? before region = some after)
    (different : other ≠ region.storageId) :
    after.backings.lookup other = before.backings.lookup other := by
  have admitted := installInitializedRegion?_admitted success
  unfold installInitializedRegion? at success
  rw [if_pos admitted] at success
  change (before.installBacking? region.storageId region.backingRecord).bind
    (fun withBacking => withBacking.allocate? region.allocId region.allocationRecord) =
      some after at success
  rw [Option.bind_eq_some_iff] at success
  obtain ⟨withBacking, installed, allocated⟩ := success
  unfold Grass.Memory.MemoryState.installBacking? at installed
  cases hbacking : before.backings.lookup region.storageId with
  | some prior => simp [hbacking] at installed
  | none =>
    simp [hbacking] at installed
    subst withBacking
    unfold Grass.Memory.MemoryState.allocate? at allocated
    split at allocated
    · contradiction
    · injection allocated with result
      subst after
      exact Grass.Std.Logical.FiniteMap.lookup_insert_ne _ different _

/-- Exact installed records expose every described byte as initialized. -/
theorem InitializedRegion.cellAt?_of_lookups {memory : Grass.Memory.MemoryState}
    {region : InitializedRegion} {offset : Nat} {byte : Byte}
    (allocation : memory.allocations.lookup region.allocId = some region.allocationRecord)
    (backing : memory.backings.lookup region.storageId = some region.backingRecord)
    (hbyte : region.bytes.get? offset = some byte) :
    memory.cellAt? region.allocId offset = some (byte, true) := by
  have offsetBound : offset < region.bytes.length :=
    (Grass.Std.Logical.Vec.get?_isSome_iff region.bytes offset).mp (by simp [hbyte])
  have valid : region.allocationRecord.extent.Contains (Grass.Memory.ByteRange.mk offset 1) ∧
      (region.allocationRecord.extent.shift region.allocationRecord.mapping.origin).WithinBound
        region.backingRecord.capacity := by
    simp [InitializedRegion.allocationRecord, InitializedRegion.backingRecord,
      Grass.Memory.AllocationRecord.mapping, Grass.Memory.ByteRange.Contains,
      Grass.Memory.ByteRange.WithinBound, Grass.Memory.ByteRange.stop,
      Grass.Memory.ByteRange.shift]
    omega
  have resolvedSome :
      (Grass.Memory.Coordinates.resolveRange? region.allocationRecord.mapping
        region.allocationRecord.extent region.backingRecord.capacity
        (Grass.Memory.ByteRange.mk offset 1)).isSome = true :=
    (Grass.Memory.Coordinates.resolveRange?_isSome_iff _ _ _ _).mpr valid
  cases resolved : Grass.Memory.Coordinates.resolveRange? region.allocationRecord.mapping
      region.allocationRecord.extent region.backingRecord.capacity
      (Grass.Memory.ByteRange.mk offset 1) with
  | none => simp [resolved] at resolvedSome
  | some span =>
    unfold Grass.Memory.MemoryState.cellAt?
    rw [allocation]
    simp [InitializedRegion.allocationRecord]
    change (memory.backings.lookup region.storageId).bind (fun store =>
      (Grass.Memory.Coordinates.resolveRange? region.allocationRecord.mapping
          region.allocationRecord.extent store.capacity
          (Grass.Memory.ByteRange.mk offset 1)).bind fun _ => store.cellAt? offset) =
        some (byte, true)
    rw [backing]
    simp only [Option.bind_some]
    rw [resolved]
    simp only [Option.bind_some]
    unfold Grass.Memory.BackingRecord.cellAt?
    change (Grass.Memory.ByteStore.empty.write 0 region.bytes.toList true).cellAt? offset =
      some (byte, true)
    rw [Grass.Memory.ByteStore.cellAt?_write_of_covers]
    · simpa [Grass.Std.Logical.Vec.get?] using hbyte
    · simpa [Grass.Memory.ByteRange.Covers, Grass.Memory.ByteRange.stop,
        Grass.Std.Logical.Vec.length] using
        (show 0 ≤ offset ∧ offset < region.bytes.length from ⟨Nat.zero_le _, offsetBound⟩)

/-- A successful installation supplies the lookup facts needed for cell observation. -/
theorem installInitializedRegion?_cellAt? {before after : Grass.Memory.MemoryState}
    {region : InitializedRegion} {offset : Nat} {byte : Byte}
    (success : installInitializedRegion? before region = some after)
    (hbyte : region.bytes.get? offset = some byte) :
    after.cellAt? region.allocId offset = some (byte, true) :=
  InitializedRegion.cellAt?_of_lookups (installInitializedRegion?_allocation success)
    (installInitializedRegion?_backing success) hbyte

end Grass.Platform.Win32
