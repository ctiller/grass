import Grass.Memory.Apply

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

It also pins the two things placement is *not*. It is not aliasing, since two
allocations may share a base and remain distinct storage until `MemoryState.aliases`
says otherwise; and it is not *authority*, in the narrow sense
`placement_is_not_authority` states — an unplaced allocation is live, readable and
writable exactly as a placed one is. What it is not any more is invisible to
`denialOf`, which reads `base` in two clauses; four docstrings in this tree still
said otherwise a round after the plan recorded the correction, one of them
thirty-two lines from its own retraction.
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

private def contexts : FreshSupply ContextTag := .initial

/-- The context these allocations belong to, and the one every descriptor below runs
in. The theorems here are not about who accesses; the field has no default, so this
file says whose storage it is rather than leaving it unowned by accident. -/
def someContext : ContextId := contexts.fresh.1

/-- Four kilobytes based at `0x1000`. -/
def placedRecord : AllocationRecord :=
  { extent := ⟨0, 4096⟩, epoch := epoch, space := .cpuVirtual
    source := .virtualAlloc, owners := [someContext]
    permission := .readWrite, live := true, bytes := .empty, base := some 0x1000 }

/-- The same shape, with nowhere to be. -/
def unplacedRecord : AllocationRecord :=
  { placedRecord with base := Option.none }

/-- A state holding both. -/
def state : MemoryState :=
  (MemoryState.empty.allocateAll?
    [(placed, placedRecord), (unplaced, unplacedRecord)]).getD .empty

/-- Both allocations happened, so `getD` did not fall back. -/
theorem the_allocations_succeed :
    (MemoryState.empty.allocateAll?
      [(placed, placedRecord), (unplaced, unplacedRecord)]).isSome := by decide

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

/-- **Placement is not authority**, in the sense that matters: the unplaced
allocation is live, readable and writable exactly as the placed one is, and the two
records differ in nothing but where they sit.

`MetadataAt` no longer compares equal, and the change is deliberate.
`AllocationRecord.base`'s docstring used to say "nothing in `denialOf` reads this",
which was true and was the problem — an access declared an address and nothing
compared it to the placement, so every Spike 1 fixture's address contradicted the
placement the same fixture built. `denialOf` reads the base now, so the base is part
of the metadata view a decision depends on, and this theorem states the property it
was written for rather than the equality that happened to hold. -/
theorem placement_is_not_authority :
    (state.MetadataAt placed).map (fun m => (m.extent, m.epoch, m.space, m.permission, m.live)) =
      (state.MetadataAt unplaced).map
        (fun m => (m.extent, m.epoch, m.space, m.permission, m.live)) ∧
    (state.MetadataAt placed).bind (fun m => m.base) ≠
      (state.MetadataAt unplaced).bind (fun m => m.base) := by
  exact ⟨by decide, by decide⟩

/-! ## An extent that does not start at zero

`denialOf`'s wrap clause bounded by `extent.size` and the addresses an access can
reach run to `extent.stop`. Review placed an allocation with a non-zero
`extent.start` past the wrap point and had its store admitted at an address inside a
second, unrelated live allocation — with `SharesBytes` false between the two, so it
is not §4.4.1b's same-base case. These are that state, refused.
-/

/-- A third allocation, whose extent starts at 200 and ends at 250. -/
def offsetAlloc : AllocId := allocs.fresh.2.fresh.2.fresh.1

/-- Based so that offset 200 lands at address 100 — past the wrap. Its *size* is 50,
which fits; its *stop* is 250, which does not. -/
def offsetRecord : AllocationRecord :=
  { extent := ⟨200, 50⟩, epoch := epoch, space := .cpuVirtual
    source := .virtualAlloc, owners := [someContext]
    permission := .readWrite, live := true, bytes := .empty
    base := some (0 - 100) }

/-- A state holding it beside the placed allocation, which sits at `0x1000`. -/
def wrapped : MemoryState :=
  (state.allocate? offsetAlloc offsetRecord).getD state

/-- The allocation is there, and the two are not aliases — so any collision below is
a placement collision rather than a declared one. -/
theorem the_wrapped_allocation_is_there :
    (wrapped.allocations.lookup offsetAlloc).isSome ∧
    ¬ wrapped.SharesBytes offsetAlloc placed := by
  exact ⟨by decide, by decide⟩

/-- **The wrap is refused.** With the clause bounded by `extent.size` this allocation
passed, because 50 bytes fit anywhere. -/
theorem the_offset_wrap_is_refused :
    denialOf wrapped
      { context := someContext, address := .numeric 100, space := .cpuVirtual
        provenance :=
          { space := .cpuVirtual, root := offsetAlloc, epoch := epoch
            source := .virtualAlloc, rootExtent := ⟨200, 50⟩, path := [] }
        range := ⟨200, 8⟩, intent := .write, requiredPermission := .readWrite
        alignment := 1, initialization := .readsNothing
        producesInitialized := true } = some AuditViolationClass.placementWraps := by
  decide

/-- And an allocation with the same non-zero start that does *not* wrap is still
admitted, so the clause did not simply become "refuse a non-zero start". -/
def fitting : MemoryState :=
  (state.allocate? offsetAlloc { offsetRecord with base := some 0x2000 }).getD state

theorem an_offset_allocation_that_fits_is_admitted :
    (fitting.allocations.lookup offsetAlloc).isSome ∧
    denialOf fitting
      { context := someContext, address := .numeric (0x2000 + 200), space := .cpuVirtual
        provenance :=
          { space := .cpuVirtual, root := offsetAlloc, epoch := epoch
            source := .virtualAlloc, rootExtent := ⟨200, 50⟩, path := [] }
        range := ⟨200, 8⟩, intent := .write, requiredPermission := .readWrite
        alignment := 1, initialization := .readsNothing
        producesInitialized := true } = Option.none := by
  exact ⟨by decide, by decide⟩

end Tests.Memory.Placement
