import Grass.Memory.SpatialAccess

/-!
# Spatial access controls

These fixtures construct one placed object through the public backing and
allocation doors, then resolve that object's real provenance in the exact
constructed machine state. This is a model-state anchor, not a concrete-reachability
proof. The candidate footprints remain independent spatial inputs: no fixture
claims that an ISA instruction attempted or committed either write.
-/

namespace Tests.Memory.SpatialAccess

open Grass.Core Grass.Memory Grass.Memory.SpatialAccess Grass.Std.Logical

private def allocs : FreshSupply AllocTag := .initial
private def backings : FreshSupply StorageTag := .initial
private def contexts : FreshSupply ContextTag := .initial

private def allocation : AllocId := allocs.fresh.1
private def backing : StorageId := backings.fresh.1
private def caller : ContextId := contexts.fresh.1
private def epoch : EpochId := (FreshSupply.initial (Tag := EpochTag)).fresh.1

/-- The root allocation has room beyond the eight-byte object. This makes the
escaping footprint an object-boundary failure rather than an allocation-boundary
failure. -/
private def allocationRecord : AllocationRecord :=
  { extent := ⟨0, 16⟩, epoch := epoch, space := .cpuVirtual
    source := .virtualAlloc, owners := [caller], permission := .readWrite, live := true
    backing := backing, origin := 0, base := some 0x1000 }

private def backingRecord : BackingRecord := { capacity := 16, bytes := .empty }

private def objectStep : ProvenanceStep :=
  { kind := .object, label := ⟨"eight-byte-object"⟩, extent := ⟨0, 8⟩ }

private def provenance : Provenance :=
  { space := .cpuVirtual, root := allocation, epoch := epoch
    source := .virtualAlloc, rootExtent := ⟨0, 16⟩, path := [objectStep] }

private def memory? : Option MemoryState := do
  let state ← MemoryState.empty.installBacking? backing backingRecord
  state.allocate? allocation allocationRecord

/-- The fixture never substitutes a fallback state: the proof is consumed by
`Option.get` below. -/
theorem checked_memory_setup_succeeds : memory?.isSome := by decide

private def memory : MemoryState := memory?.get (by decide)
private def machine : MachineState := MachineState.initial memory

/-- The object certificate is extracted from the resolver at this exact reached
machine state. -/
private def resolvedObject :
    machine.memory.ResolvedAccess provenance provenance.extent :=
  (machine.memory.resolveAccess? provenance provenance.extent).toOption.get (by decide)

theorem live_object_resolves_in_the_reached_state :
    machine.memory.resolveAccess? provenance provenance.extent = .ok resolvedObject :=
  MemoryState.resolveAccess?_eq_ok resolvedObject

private theorem objectAllocation_eq : resolvedObject.allocation = allocationRecord := by
  apply Option.some.inj
  exact resolvedObject.allocationLookup.symm.trans (by decide)

private theorem allocationPlacement_does_not_wrap :
    FitsAllocation (0x1000 : MachineAddress) allocationRecord.extent.stop := by
  change (0x1000 : MachineAddress).toNat + 16 ≤ 2 ^ 64
  have hbase : (0x1000 : MachineAddress).toNat = 4096 := by decide
  have hpow : (2 : Nat) ^ 13 ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have h13 : (8192 : Nat) = 2 ^ 13 := by decide
  omega

private def placedObject : PlacedObject machine.memory provenance where
  resolved := resolvedObject
  base := 0x1000
  placed := by
    rw [objectAllocation_eq]
    rfl
  noWrap := by
    rw [objectAllocation_eq]
    exact allocationPlacement_does_not_wrap

private theorem safeFootprint_does_not_wrap :
    FitsAllocation (0x1004 : MachineAddress) 4 := by
  change (0x1004 : MachineAddress).toNat + 4 ≤ 2 ^ 64
  have hbase : (0x1004 : MachineAddress).toNat = 4100 := by decide
  have hpow : (2 : Nat) ^ 13 ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have h13 : (8192 : Nat) = 2 ^ 13 := by decide
  omega

private def safeFootprint : WriteFootprint :=
  { address := 0x1004, size := 4, noWrap := safeFootprint_does_not_wrap }

/-- Bytes at addresses `base + 4` through `base + 7` are all inside the live
eight-byte object. -/
theorem safe_footprint_has_no_outside_byte :
    outsideIndex? placedObject safeFootprint = none := by decide

theorem every_safe_footprint_byte_is_within_the_object :
    WithinObject placedObject safeFootprint :=
  (outsideIndex?_eq_none_iff placedObject safeFootprint).mp
    safe_footprint_has_no_outside_byte

private theorem escapingFootprint_does_not_wrap :
    FitsAllocation (0x1008 : MachineAddress) 4 := by
  change (0x1008 : MachineAddress).toNat + 4 ≤ 2 ^ 64
  have hbase : (0x1008 : MachineAddress).toNat = 4104 := by decide
  have hpow : (2 : Nat) ^ 13 ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have h13 : (8192 : Nat) = 2 ^ 13 := by decide
  omega

private def escapingFootprint : WriteFootprint :=
  { address := 0x1008, size := 4, noWrap := escapingFootprint_does_not_wrap }

/-- The first byte at `base + 8` is already outside the eight-byte object, even
though it still lies within the sixteen-byte live root allocation. -/
theorem escaping_footprint_reports_its_first_byte :
    outsideIndex? placedObject escapingFootprint = some 0 := by decide

theorem escaping_footprint_exhibits_an_outside_machine_address :
    OutsideByte placedObject escapingFootprint 0 :=
  outsideIndex?_sound placedObject escapingFootprint
    escaping_footprint_reports_its_first_byte

theorem escaping_footprint_is_not_within_the_object :
    ¬ WithinObject placedObject escapingFootprint :=
  OutsideByte.not_within escaping_footprint_exhibits_an_outside_machine_address

private theorem emptyFootprint_does_not_wrap :
    FitsAllocation (0x2000 : MachineAddress) 0 := by
  change (0x2000 : MachineAddress).toNat ≤ 2 ^ 64
  have hbase : (0x2000 : MachineAddress).toNat = 8192 := by decide
  have hpow : (2 : Nat) ^ 13 ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  rw [hbase]
  exact hpow

private def emptyFootprint : WriteFootprint :=
  { address := 0x2000, size := 0, noWrap := emptyFootprint_does_not_wrap }

/-- An empty footprint has no byte witness even when its position is outside the
object. This is why the exact safe result is `WithinObject`, not positional
`ByteRange.Contains`. -/
theorem empty_footprint_has_no_outside_byte :
    outsideIndex? placedObject emptyFootprint = none := by decide

theorem empty_footprint_is_vacuously_within_the_object :
    WithinObject placedObject emptyFootprint :=
  (outsideIndex?_eq_none_iff placedObject emptyFootprint).mp
    empty_footprint_has_no_outside_byte

/-- A two-byte footprint beginning at the largest machine address cannot be
constructed: `WriteFootprint.noWrap` rejects the modular-wrap ambiguity before
spatial comparison. -/
theorem wrapping_candidate_has_no_footprint :
    ¬ FitsAllocation (0 - 1 : MachineAddress) 2 := by
  unfold FitsAllocation
  have hmax : (0 - 1 : MachineAddress).toNat = 2 ^ 64 - 1 := by simp
  omega

end Tests.Memory.SpatialAccess
