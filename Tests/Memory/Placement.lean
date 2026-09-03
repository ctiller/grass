import Grass.Memory.State

/-!
# Placement, instantiated

`Grass/Memory/Range.lean` records from its first line that `Nat` disjointness says
nothing about machine addresses, and `Grass/Memory/Addressing.lean` proves the
arithmetic that closes the gap. For several milestones nothing could *use* that
proof, because no allocation carried an address — the module was imported by the
axiom audit and by nothing else, and `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2
listed the debt as undischarged.

This file is the check that it is discharged: the bridge applies to a state built
the ordinary way, not only to a hypothetical one.

It also pins the two things placement is *not*. It is not authority — `denialOf`
reads none of it — and it is not aliasing, since two allocations may share a base
and remain distinct storage until `MemoryState.aliases` says otherwise.
-/

namespace Tests.Memory.Placement

open Grass.Core Grass.Memory Grass.Std.Logical

private def allocs : FreshSupply AllocTag := .initial

/-- A placed allocation. -/
def placed : AllocId := allocs.fresh.1

/-- A second allocation, deliberately left unplaced: a logical address space has
allocations with no machine address, which is why the base is an `Option`. -/
def unplaced : AllocId := allocs.fresh.2.fresh.1

private def epoch : EpochId := (FreshSupply.initial (Tag := EpochTag)).fresh.1

/-- Four kilobytes based at `0x1000`. -/
def placedRecord : AllocationRecord :=
  { extent := ⟨0, 4096⟩, epoch := epoch, space := .cpuVirtual
    permission := .readWrite, live := true, bytes := .empty, base := some 0x1000 }

/-- The same shape, with nowhere to be. -/
def unplacedRecord : AllocationRecord :=
  { placedRecord with base := Option.none }

/-- A state holding both. -/
def state : MemoryState :=
  (MemoryState.empty.allocate placed placedRecord).allocate unplaced unplacedRecord

/-- The placed allocation does not wrap, which is the hypothesis every bridge lemma
takes. Proved rather than decided: `FitsAllocation` bounds by `2 ^ 64`, and asking
the kernel to evaluate that is how a fixture stops finishing. -/
theorem placed_does_not_wrap : state.PlacedWithoutWrap placed := by
  intro record hrec base hbase
  have hlook : state.allocations.lookup placed = some placedRecord := by decide
  rw [hlook] at hrec
  have hr : record = placedRecord := by simpa using hrec.symm
  subst hr
  have hb : base = 0x1000 := by
    have hbr : placedRecord.base = some (0x1000 : MachineAddress) := rfl
    rw [hbr] at hbase
    simpa using hbase.symm
  subst hb
  show (0x1000 : MachineAddress).toNat + (4096 : Nat) ≤ 2 ^ 64
  have hsmall : (0x1000 : MachineAddress).toNat = 4096 := by decide
  have hpow : (2 : Nat) ^ 13 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
  have h13 : (8192 : Nat) = 2 ^ 13 := by decide
  omega

/--
**Two disjoint ranges in a placed allocation do not alias.**

The offset-to-address bridge, applied. The two ranges are `[0, 8)` and `[8, 16)`,
whose offsets are adjacent — the case where `Nat` reasoning is least informative
about addresses and where an off-by-one in `addressOf` would show.
-/
theorem disjoint_offsets_have_distinct_addresses (i j : Nat)
    (hi : (ByteRange.mk 0 8).Covers i) (hj : (ByteRange.mk 8 8).Covers j) :
    state.addressAt? placed i ≠ state.addressAt? placed j :=
  MemoryState.addressAt?_ne_of_disjoint (record := placedRecord) (base := 0x1000)
    placed_does_not_wrap (by decide) (by decide) (by decide) (by decide) hi hj rfl

/-- The addresses are the ones arithmetic says, so the theorem above is about a
real placement rather than a vacuous one. -/
theorem the_addresses_are_where_expected :
    state.addressAt? placed 0 = some 0x1000 ∧
    state.addressAt? placed 8 = some 0x1008 := by decide

/-- An unplaced allocation has no address, and asking is not an error. This is the
case a mandatory base would have forced a profile to invent. -/
theorem unplaced_has_no_address : state.addressAt? unplaced 0 = Option.none := by decide

/-- Placement is not authority: the unplaced allocation is live, readable and
writable exactly as the placed one is. Nothing in `denialOf` reads a base. -/
theorem placement_is_not_authority :
    state.MetadataAt placed = state.MetadataAt unplaced := by decide

end Tests.Memory.Placement
