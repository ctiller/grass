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

/-! ## The address a descriptor declares must be the one its placement gives

`AuditViolationClass.addressDisagreesWithPlacement` repairs a demonstrated defect --
its docstring records that every address in the Spike 1 fixtures contradicted the
placement the same fixture built, and that six of `Tests/Op/FakeIsa.lean`'s own
descriptors named an address belonging to a different allocation. Nothing tested it:
review deleted the clause and the whole tree stayed green, so the repair could have
been undone invisibly. -/

/-- The `fitting` allocation accessed at the address a *different* live allocation is
based at. Every other clause of `denialOf` passes: the allocation is live, in the
right epoch and space, its extent agrees with the provenance, the range is inside it,
the placement does not wrap and the permission covers the intent. -/
theorem an_address_from_another_allocation_is_refused :
    denialOf fitting
      { context := someContext, address := .numeric 0x1000, space := .cpuVirtual
        provenance :=
          { space := .cpuVirtual, root := offsetAlloc, epoch := epoch
            source := .virtualAlloc, rootExtent := ⟨200, 50⟩, path := [] }
        range := ⟨200, 8⟩, intent := .write, requiredPermission := .readWrite
        alignment := 1, initialization := .readsNothing
        producesInitialized := true } =
      some AuditViolationClass.addressDisagreesWithPlacement := by
  decide

/-- `0x1000` is not an arbitrary wrong address: it is where `placed` sits, so the
refusal above is about *which* allocation the address belongs to rather than about an
address belonging to none. `an_offset_allocation_that_fits_is_admitted` is the
positive control -- the same descriptor at the address `fitting`'s own placement gives
is denied nothing. -/
theorem the_wrong_address_is_another_allocations_base :
    (fitting.allocations.lookup placed).map AllocationRecord.base = some (some 0x1000) ∧
    (fitting.allocations.lookup offsetAlloc).map AllocationRecord.base =
      some (some 0x2000) := by
  exact ⟨by decide, by decide⟩

/-! ## The bounds clause fires through the block evaluator, and only there

`the_bounds_clause_cannot_fire` proves that `step` never reaches `denialOf`'s bounds
clause: well-formedness supplies nesting and containment and the extent clause forces
the record's extent to equal the declared root extent. `applyAccess` asks `denialOf`
with no well-formedness hypothesis, so for a block descriptor the clause is the only
thing between the access and a write outside its allocation. Nothing tested it --
`outOfBounds` appeared nowhere under `Tests/` except in one prose comment. -/

/-- A block store reaching far past the allocation it names. Every other clause of
`denialOf` passes: the allocation is live, in the right epoch, space and source, its
extent agrees with the provenance's declared root extent, the placement does not wrap,
the declared address is the one the placement gives, and the permission covers the
intent. -/
def overrunningStore : AccessDescriptor :=
  { context := someContext, address := .numeric (0x2000 + 200), space := .cpuVirtual
    provenance :=
      { space := .cpuVirtual, root := offsetAlloc, epoch := epoch
        source := .virtualAlloc, rootExtent := ⟨200, 50⟩, path := [] }
    range := ⟨200, 4096⟩, intent := .write, requiredPermission := .readWrite
    alignment := 1, initialization := .readsNothing
    producesInitialized := true }

/-! ### Both inequalities of the bounds clause

`ByteRange.Contains r s` is `r.start ≤ s.start ∧ s.stop ≤ r.stop`, and
`overrunningStore` starts exactly where its allocation does, so its refusal exercises
the upper inequality alone. Review weakened the clause to that inequality and the whole
tree stayed green: a block access could underrun into bytes below an allocation whose
extent does not start at zero, which is the only kind this fixture family has.

This is the third `Contains` guard found pinned in one direction — `issue?`'s
containment clause was the first and `MayLend`'s sublet bound the second — so the sweep
this time was over every call site rather than the one review named.
`an_underrunning_block_access_is_refused` is the missing half here,
`a_borrower_may_not_sublet_below_what_it_holds` in `Tests/Op/StandardLoan.lean`, and
`a_range_below_the_provenance_is_refused` in `Tests/Memory/WellFormedClauses.lean`. -/

/-- **A block access outside its allocation is refused.** -/
theorem a_block_access_out_of_bounds_is_refused :
    denialOf fitting overrunningStore = some AuditViolationClass.outOfBounds := by
  decide

/-- The same store with a range that fits is denied nothing, so the refusal is the
bound and not the descriptor. -/
theorem the_same_block_access_inside_the_allocation_is_admitted :
    denialOf fitting { overrunningStore with range := ⟨200, 8⟩ } = Option.none := by
  decide

/-- And the refusal changes nothing, which is what makes it a refusal rather than a
partial write. `applyAccess_refused_preserves_state` is stated over an arbitrary state;
this discharges its hypothesis for a concrete one, so the block evaluator really does
leave `fitting` alone. -/
theorem the_refused_block_access_changes_nothing :
    applyAccess fitting overrunningStore (List.replicate 4096 0) (fun _ => 0) =
      (.refused AuditViolationClass.outOfBounds, fitting) :=
  applyAccess_refused_preserves_state fitting overrunningStore _ _
    a_block_access_out_of_bounds_is_refused

/-! ## The four clauses ahead of the bounds clause, which nothing discriminated

`AuditViolationClass.emittedByTransition` declares the classes a profile must
recognize — `AuditViolationClass.emittedByTransition_length` is how many, stated as a
theorem because this sentence carried the number and went stale four times. Two of them -- `wrongAddressSpace` and `deadProvenance` -- appeared nowhere
under `Tests/` at all, and review switched off each of the four `denialOf` clauses that
produce them with the tree staying green.

They matter most on the block path, for the reason
`a_block_access_out_of_bounds_is_refused` above already gives: `applyAccess` asks
`denialOf` with no well-formedness hypothesis, so these clauses are the only thing
between a block descriptor and a write into storage the table does not hold, into a
torn-down allocation, or through a stale-epoch provenance -- §2's "address reuse never
revives old pointers", as a committed write. On the `step` path `authorityOf` reports
`unavailable` for a dead provenance, so the access is refused anyway, under the wrong
class. -/

/-- A fourth allocation, torn down. -/
def freedAlloc : AllocId := allocs.fresh.2.fresh.2.fresh.2.fresh.1

/-- A fifth the table never holds, so a descriptor may name it. -/
def absentAlloc : AllocId := allocs.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- A second epoch, so a provenance can be stale. -/
private def laterEpoch : EpochId := (FreshSupply.initial (Tag := EpochTag)).fresh.2.fresh.1

/-- The `fitting` state with a dead allocation beside it. -/
def withFreed : MemoryState :=
  (fitting.allocate? freedAlloc { placedRecord with live := false }).getD fitting

/-- The four descriptors below differ from `overrunningStore` in one field each, and
the state holds what they name -- so each refusal is the clause it is named for. -/
theorem the_liveness_fixtures_are_real :
    (withFreed.allocations.lookup freedAlloc).map AllocationRecord.live = some false ∧
    withFreed.allocations.lookup absentAlloc = Option.none ∧
    (withFreed.allocations.lookup offsetAlloc).map AllocationRecord.live = some true ∧
    (withFreed.allocations.lookup offsetAlloc).map AllocationRecord.epoch = some epoch ∧
    laterEpoch ≠ epoch := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **And one underrunning it.** `offsetAlloc`'s extent starts at 200, so a range at
zero lies below the allocation while inside the address space — the lower inequality of
`Contains`, which nothing exercised. -/
theorem an_underrunning_block_access_is_refused :
    (⟨0, 8⟩ : ByteRange).stop ≤ offsetRecord.extent.stop ∧
    denialOf fitting
      { overrunningStore with
        range := ⟨0, 8⟩, address := .numeric 0x2000 } =
      some AuditViolationClass.outOfBounds := by
  exact ⟨by decide, by decide⟩

/-- The same store bounded to eight bytes, which `withFreed` admits: the control every
refusal below is measured against. -/
def fittingStore : AccessDescriptor := { overrunningStore with range := ⟨200, 8⟩ }

/-- It is admitted, so the four refusals are their clauses and not the descriptor. -/
theorem the_fitting_store_is_admitted :
    denialOf withFreed fittingStore = Option.none := by decide

/-- **A provenance the allocation table does not hold is refused.** -/
theorem an_absent_allocation_is_refused :
    denialOf withFreed
      { fittingStore with provenance := { fittingStore.provenance with root := absentAlloc } } =
      some AuditViolationClass.provenanceNotAllocated := by decide

/-- **A torn-down allocation is refused**, which is §5's teardown read at the access. -/
theorem a_dead_allocation_is_refused :
    denialOf withFreed
      { fittingStore with provenance := { fittingStore.provenance with root := freedAlloc } } =
      some AuditViolationClass.deadProvenance := by decide

/-- **A stale-epoch provenance is refused**, which is §2's "address reuse never revives
old pointers" at the access.

The record is *live* here, which `the_freed_allocation_is_the_one_that_is_dead` below
pins: these three theorems had three docstrings naming three conditions and all three
asserted `deadProvenance`, so the class threw away the distinction the file had already
made. Each names its own class now. -/
theorem a_stale_epoch_is_refused :
    denialOf withFreed
      { fittingStore with provenance := { fittingStore.provenance with epoch := laterEpoch } } =
      some AuditViolationClass.staleEpoch := by decide

/-- The three refusals above are three conditions and not one: the identity the first
names is absent from the table, the second's record is torn down, and the third's is
**live** and merely at another epoch. Without this the three classes would be three
names for whatever `withFreed` happens to contain. -/
theorem the_freed_allocation_is_the_one_that_is_dead :
    withFreed.allocations.lookup absentAlloc = Option.none ∧
    (withFreed.allocations.lookup freedAlloc).any (fun r => !r.live) = true ∧
    (withFreed.allocations.lookup offsetAlloc).any (fun r => r.live) = true := by
  exact ⟨by decide, by decide, by decide⟩

/-- **And a provenance naming a different address space is refused.** §7.5 makes
spaces non-interchangeable, and this clause is the only comparison of the *record's*
space with the provenance's anywhere in the layer: `WellFormedIn.spaceAgrees` relates
the descriptor to itself, admissibility resolves the descriptor's space in the profile's
table, and `authorityOf` reads neither. -/
theorem a_provenance_in_another_space_is_refused :
    denialOf withFreed
      { fittingStore with provenance :=
        { fittingStore.provenance with space := .deviceHostVisible } } =
      some AuditViolationClass.wrongAddressSpace := by decide

/-! ## The block evaluator commits a misaligned store

`denialOf` has no alignment branch, and `Grass/Memory/Apply.lean` gives the reason:
`AccessDescriptor.WellFormedIn.aligned` checks it and `step` requires well-formedness
before any access is attempted, so a branch here would be unreachable. That was written
unqualified and it is true only of the transition path. `applyAccess` asks `denialOf`
with no well-formedness hypothesis at all -- the same fact that makes the bounds clause
live, recorded forty lines below the alignment paragraph in the same file -- so on the
block path nothing stands between a misaligned descriptor and a committed write.

Kept as a demonstration rather than a guard, on the model of
`a_join_of_two_duties_halves_the_ledger`: closing this breaks a theorem rather than
passing unnoticed. Closing it means either an alignment clause in `denialOf`, which
would be unreachable through `step` and would put a fifteenth class into
`emittedByTransition`, or a well-formedness hypothesis on `applyAccess`, which changes
the block evaluator's signature. `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records
the choice as open. -/

/-- A four-byte store at offset 201 of the `fitting` allocation, demanding page
alignment at an address that is not page-aligned. Every clause of `denialOf` passes:
the address really is the allocation's base plus the offset, which is what the
placement clause checks. -/
def misalignedStore : AccessDescriptor :=
  { overrunningStore with
    range := ⟨201, 4⟩, address := .numeric (0x2000 + 201), alignment := 4096 }

/-- **It is misaligned and it is not denied.** -/
theorem a_misaligned_block_access_is_not_denied :
    ¬ misalignedStore.AlignmentSatisfied ∧
    ¬ misalignedStore.WellFormedIn AddressSpace.cpuVirtual64 ∧
    denialOf fitting misalignedStore = Option.none := by
  exact ⟨by decide, by decide, by decide⟩

/-- **And the block evaluator commits it**, which is the consequence. The second
conjunct is the byte: offset 201 held nothing and holds `0xAB` afterwards. -/
theorem a_misaligned_block_access_commits :
    (applyAccess fitting misalignedStore (List.replicate 4 0xAB) (fun _ => 0)).1.Committed ∧
    (applyAccess fitting misalignedStore (List.replicate 4 0xAB)
      (fun _ => 0)).2.byteAt? offsetAlloc 201 = some 0xAB ∧
    fitting.byteAt? offsetAlloc 201 = Option.none := by
  exact ⟨by decide, by decide, by decide⟩

/-- The same store at a page-aligned address is well formed, so the fixture is about
the alignment and not about the descriptor. -/
theorem the_aligned_store_is_well_formed :
    ({ misalignedStore with alignment := 1 } :
      AccessDescriptor).WellFormedIn AddressSpace.cpuVirtual64 := by decide

/-! ## A view mapped at a non-zero offset

`MemoryState.aliases` carried no offset until now, so aliased allocations were
assumed to agree byte for byte from zero. The ordinary `MapViewOfFile` case -- a view
mapped part-way into a file -- was not expressible, and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` section 4.4.1 recorded that as this layer's
largest open gap.

These are the states that gap made unrepresentable. They are here rather than in
`Tests/Memory/Loans.lean` because the question is about placement and offsets rather
than about authority: nothing below issues a grant.
-/

/-- A view of `placed`, mapped 2048 bytes in. -/
def viewAt2048 : AllocId := allocs.fresh.2.fresh.2.fresh.2.fresh.1

/-- A view of *that* view, a further 256 bytes in. -/
def viewAt256More : AllocId := allocs.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- `placed`, and two views into it at non-zero offsets, chained. -/
def mapped : MemoryState :=
  (((MemoryState.empty.allocateAll?
      [(placed, placedRecord), (viewAt2048, placedRecord),
       (viewAt256More, placedRecord)]).getD .empty).alias placed viewAt2048 2048).alias
    viewAt2048 viewAt256More 256

/-- The offset is recorded, and it is the offset that was declared. -/
theorem the_view_is_mapped_at_its_offset :
    mapped.SharesBytesAt placed viewAt2048 2048 := by decide

/-- **And not at zero**, which is the whole content of the change: the unoffset
model could only say the two share bytes, and could only mean "at the same offsets".
A model that cannot distinguish these two states cannot describe a mapped view. -/
theorem the_view_is_not_mapped_at_zero :
    ¬ mapped.SharesBytesAt placed viewAt2048 0 := by decide

/-- Backwards, the shift negates. `AliasEdge.delta` is an `Int` for exactly this: a
`Nat` would have made the reverse direction inexpressible and the relation
asymmetric. -/
theorem the_reverse_hop_negates_the_offset :
    mapped.SharesBytesAt viewAt2048 placed (-2048) := by decide

/-- **Offsets compose along a path.** Two hops at 2048 and 256 put `viewAt256More`
2304 bytes into `placed`, and no single declared edge says so. This is the
transitivity `SharesBytes` already had, now carrying an offset with it. -/
theorem offsets_compose_along_a_chain :
    mapped.SharesBytesAt placed viewAt256More 2304 := by decide

/-- The sum, and not either summand: a chain is not two independent facts. -/
theorem the_chain_is_not_its_first_hop :
    ¬ mapped.SharesBytesAt placed viewAt256More 2048 ∧
    ¬ mapped.SharesBytesAt placed viewAt256More 256 := by decide

/-- The unoffset question is unchanged, which is what makes this migration safe.
`SharesBytes` still answers "the same storage at all", conflict detection still
consults it, and every theorem stated over it is still true of these states. -/
theorem the_unoffset_relation_is_unchanged :
    mapped.SharesBytes placed viewAt2048 ∧
    mapped.SharesBytes placed viewAt256More := by decide

/-! ### One offset, or a refusal

`SharesBytesAt` holds at every shift some declared path witnesses, and deliberately
does not choose between them. `aliasShift?` is where a caller that needs *one* offset
gets an answer or is refused, which is [FOUNDATION.md](../../docs/FOUNDATION.md) law
8's direction: picking the first path, the shortest, or zero would each be a
permissive fallback.
-/

/-- On a consistent graph the offset is the one declared, and a chain's is the sum. -/
theorem the_shift_is_recovered :
    mapped.aliasShift? placed viewAt2048 = some 2048 ∧
    mapped.aliasShift? placed viewAt256More = some 2304 := by decide

/-- Reflexive at zero when nothing contradicts it. -/
theorem an_allocation_is_at_zero_from_itself :
    mapped.aliasShift? placed placed = some 0 := by decide

/-- Unrelated allocations get `none`, which is the *other* thing `none` means. -/
theorem an_unaliased_allocation_has_no_shift :
    mapped.aliasShift? placed unplaced = Option.none := by decide

/-- The same pair declared aliased twice, at offsets that disagree. A profile can
write this and the model must not pretend otherwise. -/
def contradictory : MemoryState :=
  (((MemoryState.empty.allocateAll?
      [(placed, placedRecord), (viewAt2048, placedRecord)]).getD .empty).alias
    placed viewAt2048 0).alias placed viewAt2048 8

/-- **The predicate stays permissive and the decision refuses**, which is the pairing
worth stating together. `SharesBytesAt` holds at *both* declared offsets, because
both are witnessed and it is not `SharesBytesAt`'s job to adjudicate them. -/
theorem the_predicate_admits_both_offsets :
    contradictory.SharesBytesAt placed viewAt2048 0 ∧
    contradictory.SharesBytesAt placed viewAt2048 8 := by decide

/-- And `aliasShift?` refuses rather than picking one. Law 8: no permissive
fallback. Zero is not the answer, and neither is the first edge declared. -/
theorem contradictory_offsets_are_refused :
    contradictory.aliasShift? placed viewAt2048 = Option.none := by decide

/-- The unoffset question is still answerable on the same state, and still says yes:
whatever else is true, those two allocations do share storage. A caller asking about
conflicts is not blocked by a disagreement about offsets. -/
theorem sharing_is_still_decided :
    contradictory.SharesBytes placed viewAt2048 := by decide

/-! ### Authority across a mapped view

`MemoryState.AuthorizedAt` compared a grant's range to an access offset directly,
having checked only that the two allocations share bytes. A grant's range is in its
own allocation's coordinates and the offset is in the access's, so that comparison is
right exactly when the two agree offset for offset -- which is what an alias with a
non-zero delta denies.

These are the two states where the old check and the new one disagree, in both
directions. `mapped` relates `placed` to `viewAt2048` at `+2048`, so offset `i` in
`placed` is offset `i + 2048` in the view, and the view's own offset 0 is 2048 bytes
*before* the buffer starts.
-/

/-- Provenance rooted at the buffer. -/
def placedProv : Provenance :=
  { space := .cpuVirtual, root := placed, epoch := epoch, source := .virtualAlloc
    rootExtent := ⟨0, 4096⟩, path := [] }

/-- The same storage named through the view. -/
def viewProv : Provenance := { placedProv with root := viewAt2048 }

/-- Four bytes at the view's own offset zero. -/
def grantAtViewZero : AuthorityGrant :=
  { kind := .loan, holder := someContext, lender := someContext, provenance := viewProv
    range := ⟨0, 4⟩, rights := .readWrite }

/-- Four bytes at the view's offset 2048, which is where the buffer begins. -/
def grantAtViewOffset : AuthorityGrant := { grantAtViewZero with range := ⟨2048, 4⟩ }

/-- **The old comparison would have admitted this**, and that is the bug. A plain
`Covers` says the grant's range holds offset 0, because both are the number zero. -/
theorem the_plain_range_check_admits_the_wrong_grant :
    grantAtViewZero.range.Covers 0 := by decide

/-- And the alias-aware check refuses it. The view's offset 0 is 2048 bytes before
the buffer starts, so this grant covers no byte of `placed` at all. -/
theorem authority_does_not_carry_across_the_offset :
    ¬ mapped.AuthorizedAt grantAtViewZero someContext placedProv 0 .read := by decide

/-- The other direction, and the half a purely stricter check would have lost: the
grant that *does* reach the buffer's first byte is the one at the view's offset 2048,
and the old comparison refused it. -/
theorem the_grant_at_the_mapped_offset_does_carry :
    mapped.AuthorizedAt grantAtViewOffset someContext placedProv 0 .read := by decide

/-- The old comparison on that same grant. Both theorems above are needed: a change
that only refused more could have been achieved by refusing everything. -/
theorem the_plain_range_check_refuses_the_right_grant :
    ¬ grantAtViewOffset.range.Covers 0 := by decide

/-- Sharing is not what separates them. Both grants are over storage that `placed`
shares; the offset is the whole of the difference, which is why the fix belongs in
the coverage clause and not in the sharing one. -/
theorem both_grants_are_over_shared_storage :
    mapped.SharesBytes grantAtViewZero.provenance.root placedProv.root ∧
    mapped.SharesBytes grantAtViewOffset.provenance.root placedProv.root := by decide

/-! ### Authority over torn-down storage

`MemoryState.AuthorizedAt` consulted `CurrentEpoch`, which asks only whether the
allocation's epoch matches the provenance's. `MemoryState.tearDown?` sets
`live := false` and leaves the epoch alone, so a grant over torn-down storage
satisfied the authority predicate. These are the states that showed it, written as a
probe while answering `g-construct:76` and kept because the probe is the evidence.

It was never reachable through the doors -- `issue?` refuses unless the provenance is
live, and `tearDown?` refuses while any grant is outstanding -- so the guarantee
existed as an emergent property of two guards rather than as anything stated. That is
the kind that stops holding when a third door is added.
-/

/-- The placement fixture's buffer, torn down. Succeeds because that state holds no
grants. -/
def afterTeardown : Option MemoryState := state.tearDown? [placed]

theorem the_teardown_succeeds : afterTeardown.isSome := by decide

/-- The allocation is no longer live. -/
theorem the_torn_down_allocation_is_not_live :
    ∀ s ∈ afterTeardown, ¬ s.Live placedProv := by decide

/-- **And its epoch still matches**, which is the trap. Teardown does not advance the
epoch, so every predicate that asks only about epochs still says yes. -/
theorem the_epoch_still_matches :
    ∀ s ∈ afterTeardown, s.CurrentEpoch placedProv := by decide

/-- A grant over the torn-down storage. Not reachable through `issue?`, which is the
point: this is the value the model must not authorize even though nothing can put it
in the table. -/
def ghostGrant : AuthorityGrant :=
  { kind := .loan, holder := someContext, lender := someContext
    provenance := placedProv, range := ⟨0, 4⟩, rights := .readWrite }

/-- **And it authorizes nothing.** This held before `AuthorizedAt` gained its
liveness conjunct, which is what made the conjunct worth adding: authority over
storage that is gone is not weak authority, it is none. -/
theorem a_grant_over_torn_down_storage_authorizes_nothing :
    ∀ s ∈ afterTeardown,
      ¬ s.AuthorizedAt ghostGrant someContext placedProv 0 .read := by decide

/-- The same grant against the live state, so the theorem above is about liveness and
not about some other defect in the grant. -/
theorem the_same_grant_authorizes_before_teardown :
    state.AuthorizedAt ghostGrant someContext placedProv 0 .read := by decide

/-- **And nothing in the table authorizes it either**, which is the law
`g-construct:76` asked c-mem to export for `withStack`'s exit teardown.

`MemoryState.not_granted_of_tearDown?` states it in general: after a teardown, no
grant authorizes a provenance rooted at one of the torn-down allocations, whatever
the table holds. This is that law at a concrete state, so the general statement has a
witness rather than only a proof. -/
theorem nothing_is_granted_over_torn_down_storage :
    ∀ s ∈ afterTeardown,
      ¬ s.Granted someContext placedProv ⟨0, 4⟩ .read := by decide

end Tests.Memory.Placement
