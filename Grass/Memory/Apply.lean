import Grass.Memory.Access
import Grass.Memory.State

/-!
# Applying one access to memory

`docs/INSTRUCTIONS.md` §5's bounded decidable forward fragment needs a function
that takes a descriptor and a memory state and returns what was observed and what
memory looks like afterwards. `Grass/Op/Step.lean` has that behaviour, but tangled
with event minting, obligation ledgers, and the audit ledger, so nothing could
state a law about memory alone.

`applyAccess` is that function. It is total, it is executable, and the laws below
are equations over it rather than statements about a transition's branches.

## How this relates to `step`, exactly

`applyAccess` is **not** what the transition relation calls. `Grass/Op/Step.lean`
has its own `performAccess`, which does event minting and ledger work `applyAccess`
knows nothing about, and it is `step` that a program runs through.

What ties them is `MemoryState.commitResolved`: every access that commits carries
the already checked `ResolvedAccess` through it. So the framing results here are
results about the transition, and
`Op.performAccess_frames_untouched` and `Op.runAccesses_frames_untouched` are
those results stated for `performAccess` and `runAccesses` directly.

`Op.step_frames_untouched` carries it to a whole operation. That theorem was
missing for several rounds while four documents claimed it existed, which mattered:
`runStep`'s faulting branch frames over `visibleEffects?`, which *excludes* the
faulting substep, so the survivor-list law is not a law about the step. It
quantifies over `sequence.accesses` instead, which contains both.

This is spelled out because an earlier version of this comment claimed
`applyAccess` had been *factored out of* `performAccess` when it had been written
alongside it — two write paths, framing proved about one, prose implying it
covered both. Review found it. `commitResolved` is the repair.

What is still true and worth saying plainly: a straight-line argument over
`runBlock` is an argument about `applyAccess`, not about `step`.

**They do not agree, and an earlier version of this paragraph said "the two agree on
memory".** No theorem stated it and it is false three ways, which review demonstrated.
`applyAccess` consults `denialOf`; `performAccess` consults `refusalOf`, which is
`denialOf` plus the ledger, authority-effect, authority-state, loan and race clauses —
so a store another context holds an exclusive write loan over is committed by one and
refused by the other. `performAccess` writes the bytes the outcome says committed,
`applyAccess` writes the data truncated to the range. And `performAccess` commits into
the map the declared authority effect left, while `applyAccess` cannot change the
grant map at all, so for any non-empty effect the two leave different states by
construction.

What the two *do* share is `MemoryState.commitResolved`, including the exact backing
span prepared before authority and byte checks. The framing laws below are about that
shared commit path. Anything stronger than that is unproved, and this paragraph is
where it was claimed.

## What it does not decide

Authority beyond the allocation-to-backing binding. `denialOf` checks provenance,
liveness, epoch, address space, the backing's existence and capacity, placement,
permission, initialization, and the executable backing-layout gate. Loans are
`Grass/Op/Step.lean`'s `refusalOf`, in
clauses of its own that need no policy; frames, pins and lock tokens are an
`AuthorityProvider`, which does. A caller that uses `applyAccess` alone gets memory's
own rules and neither.

## Two parameters rather than two defaults

`writeData` is what the operation writes, which a descriptor does not carry: a
descriptor says which bytes an access touches and what it may do to them, and
putting values on it would make every well-formedness proof about ranges also
about contents.

`indeterminate` is what an uninitialized byte reads as. It is reached only when a
descriptor permits reading uninitialized bytes, because `denialOf` refuses an
access demanding `.allBytesInitialized` first — so the profile that admitted such
a read is the one that owes what it observes. A zero default here would be
`docs/FOUNDATION.md` law 8's permissive fallback: the program would observe a
definite value the machine never promised.
-/

namespace Grass.Memory

open Grass.Std.Logical

/--
Why the state refuses one access, or `none` if it authorizes it.

Checked before anything commits, so a denial leaves the state exactly as it was
(`docs/MEMORY_MODEL.md` §1). The order is deliberate, so the recorded class names
the first thing that was wrong rather than an incidental consequence. Checked resolution first
distinguishes missing allocation, dead or stale provenance, address-space/source/extent
mismatch, a non-nested path, range containment, missing backing, and malformed mapping.
Placement, permission, initialization, and the temporary global backing-layout gate
follow that one resolution.

The placement clauses sit *after* bounds, and were inserted before it when they
landed. `addressOf base d.range.start` is only meaningful once the range is known to
be inside the allocation, so an out-of-bounds access whose declared address was
anything but the value that arithmetic happens to give was reported as a placement
disagreement — the audit naming a class downstream of the actual defect. Review found
it by reading this sentence against the code below it.

Alignment is deliberately absent, and the reason is narrower than it was written.
`AccessDescriptor.WellFormedIn.aligned` checks it and `step` requires well-formedness
before any access is attempted, so a misaligned access is *rejected at the
declaration*, never denied at the state.

**On the transition path.** The claim was unqualified -- "an alignment branch here
would be unreachable" -- and review falsified it the way this file falsified the same
shape for the bounds clause forty lines below: `applyAccess` asks `denialOf` with no
well-formedness hypothesis at all, so on the block path there is nothing between a
misaligned descriptor and a committed write. Review stepped a four-byte store at offset
one declaring 4096-byte alignment and watched it commit; the placement clause passes
because the declared address really is the allocation's base plus the offset, so
nothing else catches it. `Tests/Memory/Placement.lean`'s
`a_misaligned_block_access_commits` is that case, kept as a demonstration rather than a
guard, so that closing it breaks a theorem rather than passing unnoticed.

An alignment branch on the transition path would be unreachable, and an unreachable
branch that looks like a check is worse than no branch: it suggests the transition
tests something
it does not. `AuditViolationClass.misaligned` remains for a profile whose own
alignment rule is stricter than the declared demand -- reached through that profile's
`AuthorityProvider`, not through this function, which is why review removed it from
`AuditViolationClass.emittedByTransition` and why deleting it there changed nothing.

Authority beyond what an allocation record means is not here. Loans are
`Grass/Op/Step.lean`'s `refusalOf`, in two clauses of its own that need no policy at
all; frames, pins and lock tokens are an `AuthorityProvider`, which does. This is
memory's own rules, which is why it lives in the memory layer.

That sentence read "loans, frames, pins, and lock tokens are … `AuthorityProvider`"
until review found it, one milestone after `AuthorityProvider.loan` was deleted and
nineteen citations were repointed at `refusalOf`. Two were not, and both were this one
-- the sentence a reader chasing "who checks §3's loan rule" would follow. Forty lines
above, the same file already says the true thing.
-/
def MemoryState.ResolveFailure.auditClass : MemoryState.ResolveFailure → AuditViolationClass
  | .provenanceNotAllocated => .provenanceNotAllocated
  | .deadProvenance => .deadProvenance
  | .staleEpoch => .staleEpoch
  | .wrongAddressSpace => .wrongAddressSpace
  | .provenanceSourceMismatch => .provenanceSourceMismatch
  | .provenanceExtentMismatch => .provenanceExtentMismatch
  | .provenanceNotNested => .provenanceNotNested
  | .rangeOutsideProvenance => .outOfBounds
  | .backingNotAllocated => .backingNotAllocated
  | .mappingOutOfBounds => .mappingOutOfBounds

/-- The resolver outcome with its dependent evidence erased.
`MemoryState.resolveClassification_congr_metadata` uses it to state that stable
metadata preserves the precise failure class. -/
inductive MemoryState.ResolveClassification where
  | failure (reason : MemoryState.ResolveFailure)
  | resolved
deriving DecidableEq, Repr

def MemoryState.resolveClassification (state : MemoryState) (provenance : Provenance)
    (requested : ByteRange) : MemoryState.ResolveClassification :=
  match state.resolveAccess? provenance requested with
  | .error reason => .failure reason
  | .ok _ => .resolved

/-- The same classification computed from the stable metadata view. Kept private:
runtime resolution remains `resolveAccess?`; the equality below prevents this proof
projection from becoming a second executable rule. -/
private def MemoryState.resolveClassificationOfMetadata
    (metadata : Option MemoryState.AccessMetadata) (provenance : Provenance)
    (requested : ByteRange) : MemoryState.ResolveClassification :=
  match metadata with
  | none => .failure .provenanceNotAllocated
  | some access =>
      let allocation := access.allocation
      if allocation.live ≠ true then .failure .deadProvenance
      else if allocation.epoch ≠ provenance.epoch then .failure .staleEpoch
      else if allocation.space ≠ provenance.space then .failure .wrongAddressSpace
      else if allocation.source ≠ provenance.source then .failure .provenanceSourceMismatch
      else if allocation.extent ≠ provenance.rootExtent then .failure .provenanceExtentMismatch
      else if ¬ provenance.Nested then .failure .provenanceNotNested
      else if ¬ provenance.extent.Contains requested then .failure .rangeOutsideProvenance
      else match access.capacity with
        | none => .failure .backingNotAllocated
        | some capacity =>
            if (allocation.extent.shift allocation.origin).WithinBound capacity then
              .resolved
            else .failure .mappingOutOfBounds

private theorem ByteRange.shiftedWithinBound_of_extent_eq
    {allocationExtent provenanceExtent : ByteRange} {origin capacity : Nat}
    (hextent : allocationExtent = provenanceExtent)
    (hbound : (allocationExtent.shift origin).WithinBound capacity) :
    (provenanceExtent.shift origin).WithinBound capacity := by
  rwa [← hextent]

/-- Erasing dependent resolver evidence is exactly classification through
`MetadataAt`. -/
private theorem MemoryState.resolveClassification_eq_metadata (state : MemoryState)
    (provenance : Provenance) (requested : ByteRange) :
    state.resolveClassification provenance requested =
      resolveClassificationOfMetadata (state.MetadataAt provenance.root)
        provenance requested := by
  unfold resolveClassification
  cases hr : state.resolveAccess? provenance requested with
  | error failure =>
      unfold resolveAccess? at hr
      repeat' split at hr
      all_goals
        cases hr
      all_goals
        simp_all [resolveClassificationOfMetadata, MetadataAt, backingCapacity?,
          AllocationRecord.metadata]
      all_goals solve_by_elim [ByteRange.shiftedWithinBound_of_extent_eq]
  | ok access =>
      unfold resolveAccess? at hr
      repeat' split at hr
      all_goals
        cases hr
      all_goals
        simp_all [resolveClassificationOfMetadata, MetadataAt, backingCapacity?,
          AllocationRecord.metadata]
      all_goals solve_by_elim [ByteRange.shiftedWithinBound_of_extent_eq]

/-- `MetadataAt` contains every input to checked resolution except backing bytes and
allocation owners, neither of which changes its success or precise failure class. -/
theorem MemoryState.resolveClassification_congr_metadata {a b : MemoryState}
    {provenance : Provenance} {requested : ByteRange}
    (hmeta : a.MetadataAt provenance.root = b.MetadataAt provenance.root) :
    a.resolveClassification provenance requested =
      b.resolveClassification provenance requested := by
  rw [resolveClassification_eq_metadata, resolveClassification_eq_metadata, hmeta]

/-- Resolve and check one access once. The successful value is the exact checked
backing span consumed by authority, observations, events, and writes. -/
def prepareAccess (state : MemoryState) (d : AccessDescriptor) :
    Except AuditViolationClass (state.ResolvedAccess d.provenance d.range) :=
  match state.resolveAccess? d.provenance d.range with
  | .error failure => .error failure.auditClass
  | .ok access =>
      if ¬ state.DedicatedBackings then
        .error .backingLayoutUnsupported
      else if access.allocation.base.any
          (fun b => !decide (FitsAllocation b access.allocation.extent.stop)) then
        .error .placementWraps
      else if access.allocation.base.any
          (fun b => d.address != Address.numeric (addressOf b d.range.start)) then
        .error .addressDisagreesWithPlacement
      else if ¬ access.allocation.permission.Grants d.requiredPermission then
        .error .permissionDenied
      else if ¬ access.allocation.permission.Permits d.intent then
        .error .intentNotPermitted
      else if d.initialization = .allBytesInitialized ∧ ¬ access.RangeInitialized then
        .error .uninitializedRead
      else .ok access

/-- Why the prepared access was refused, if it was. -/
def denialOf (state : MemoryState) (d : AccessDescriptor) : Option AuditViolationClass :=
  match prepareAccess state d with
  | .error class_ => some class_
  | .ok _ => none

@[simp] theorem denialOf_prepareAccess_error (state : MemoryState)
    (d : AccessDescriptor) (class_ : AuditViolationClass)
    (h : prepareAccess state d = .error class_) :
    denialOf state d = some class_ := by
  simp [denialOf, h]

@[simp] theorem denialOf_prepareAccess_ok (state : MemoryState)
    (d : AccessDescriptor) (access : state.ResolvedAccess d.provenance d.range)
    (h : prepareAccess state d = .ok access) :
    denialOf state d = none := by
  simp [denialOf, h]

theorem denialOf_eq_none_iff (state : MemoryState) (d : AccessDescriptor) :
    denialOf state d = none ↔
      ∃ access : state.ResolvedAccess d.provenance d.range,
        prepareAccess state d = .ok access := by
  unfold denialOf
  cases h : prepareAccess state d with
  | error class_ => simp
  | ok access => exact ⟨fun _ => ⟨access, rfl⟩, fun _ => rfl⟩

theorem prepareAccess_ok_unique {state : MemoryState} {d : AccessDescriptor}
    {a b : state.ResolvedAccess d.provenance d.range}
    (ha : prepareAccess state d = .ok a) (hb : prepareAccess state d = .ok b) : a = b := by
  rw [ha] at hb
  exact Except.ok.inj hb

theorem resolveAccess?_of_prepareAccess {state : MemoryState} {d : AccessDescriptor}
    {access : state.ResolvedAccess d.provenance d.range}
    (h : prepareAccess state d = .ok access) :
    state.resolveAccess? d.provenance d.range = .ok access := by
  cases hr : state.resolveAccess? d.provenance d.range with
  | error failure => simp [prepareAccess, hr] at h
  | ok resolved =>
      by_cases hwrap : resolved.allocation.base.any
          (fun b => !decide (FitsAllocation b resolved.allocation.extent.stop)) = true
      <;> by_cases haddress : resolved.allocation.base.any
          (fun b => d.address != Address.numeric (addressOf b d.range.start)) = true
      <;> by_cases hgrants : resolved.allocation.permission.Grants d.requiredPermission
      <;> by_cases hpermits : resolved.allocation.permission.Permits d.intent
      <;> by_cases hinit : d.initialization = .allBytesInitialized ∧
          ¬ resolved.RangeInitialized
      <;> by_cases hdedicated : state.DedicatedBackings
      <;> simp_all [prepareAccess]

/-- A prepared access certifies the temporary executable backing profile. -/
theorem dedicatedBackings_of_prepareAccess {state : MemoryState}
    {d : AccessDescriptor} {access : state.ResolvedAccess d.provenance d.range}
    (h : prepareAccess state d = .ok access) : state.DedicatedBackings := by
  cases hr : state.resolveAccess? d.provenance d.range with
  | error failure => simp [prepareAccess, hr] at h
  | ok resolved =>
      by_cases hwrap : resolved.allocation.base.any
          (fun b => !decide (FitsAllocation b resolved.allocation.extent.stop)) = true
      <;> by_cases haddress : resolved.allocation.base.any
          (fun b => d.address != Address.numeric (addressOf b d.range.start)) = true
      <;> by_cases hgrants : resolved.allocation.permission.Grants d.requiredPermission
      <;> by_cases hpermits : resolved.allocation.permission.Permits d.intent
      <;> by_cases hinit : d.initialization = .allBytesInitialized ∧
          ¬ resolved.RangeInitialized
      <;> by_cases hdedicated : state.DedicatedBackings
      <;> simp_all [prepareAccess]

/--
**The bounds clause above cannot fire on the transition path**, which is what
`the_bounds_clause_cannot_fire` below states. It looked like a state-time check for
two milestones.

`step` admits nothing until `Substep.WellFormedIn` holds, which supplies
`provenanceNested` and `rangeInProvenance`; `denialOf`'s own extent clause, two lines
earlier, forces the allocation's extent to equal the provenance's declared root
extent. The three compose, so `record.extent.Contains d.range` is already true by the
time the bounds clause is asked. Review found it by deleting the clause and rebuilding
the tree green, then proving the reason rather than leaving it as an observation --
which is the standing rule here, after a "one check subsumes another" claim on this
branch turned out to be false within the hour.

The clause is not dead, and the first version of this paragraph said it was: it
claimed `applyAccess` "has no application anywhere under `Grass/` or `Tests/`", which
was review's observation and was wrong. `runBlock` below calls it, and
`Tests/Memory/Spike1Block.lean` and `Tests/Memory/StraightLineBlock.lean` both run
blocks and apply it directly. `applyAccess` asks `denialOf` with no well-formedness
hypothesis at all, so the bounds clause is the only thing standing between a block
descriptor and a write outside its allocation -- `Tests/Memory/Placement.lean`'s
`a_block_access_out_of_bounds_is_refused` is that case, and it is the only fixture in
the tree that reaches this branch.

So `AuditViolationClass.outOfBounds` is emitted by this layer and belongs in the
declared set; what is *not* true is the ordering sentence above, which reads as though
`step` bounds-checks the state. It does not, because `AccessDescriptor.WellFormedIn` has already asked.
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records the distinction.
-/
theorem the_bounds_clause_cannot_fire {d : AccessDescriptor} {space : AddressSpace}
    {record : AllocationRecord} (hwf : d.WellFormedIn space)
    (hext : record.extent = d.provenance.rootExtent) :
    record.extent.Contains d.range := by
  rw [hext]
  exact ByteRange.Contains.trans
    (Provenance.extent_within_root hwf.provenanceNested) hwf.rangeInProvenance

/-- What an access observed, or why it was refused. -/
structure AccessResult where
  /-- The bytes observed, if the access read and was not refused. -/
  observed : Option ByteSeq
  /-- Why it was refused, if it was. -/
  refusal : Option AuditViolationClass
deriving DecidableEq, Repr

namespace AccessResult

/-- A result that refused. -/
def refused (class_ : AuditViolationClass) : AccessResult := ⟨Option.none, some class_⟩

/-- `result.Committed` holds when the access was not refused. -/
def Committed (result : AccessResult) : Prop := result.refusal = Option.none

instance (result : AccessResult) : Decidable result.Committed :=
  inferInstanceAs (Decidable (_ = _))

end AccessResult

/-- The bytes `d` observes, reading uninitialized positions through
`indeterminate`. Always exactly `d.range.size` long. -/
def observedBytes {state : MemoryState} {d : AccessDescriptor}
    (access : state.ResolvedAccess d.provenance d.range)
    (indeterminate : Nat → Byte) : ByteSeq :=
  (List.range d.range.size).map fun i =>
    match access.byteAt? (d.range.start + i) with
    | some byte => byte
    | Option.none => indeterminate i

/-- Initialization of a prepared backing span is exactly pointwise initialization
through the allocation-local checked view. This is the bridge used to carry a
denial decision across a disjoint backing-span write. -/
theorem MemoryState.ResolvedAccess.rangeInitialized_iff_initializedAt
    {state : MemoryState} {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) :
    access.RangeInitialized ↔
      ∀ offset, requested.Covers offset → state.InitializedAt provenance.root offset := by
  constructor
  · intro h offset hcovered
    unfold MemoryState.InitializedAt
    rw [← access.cellAt?_eq_state hcovered]
    unfold MemoryState.ResolvedAccess.RangeInitialized ByteStore.Initialized at h
    have hbacking := h (access.allocation.origin + offset)
      ((Coordinates.Mapping.span_covers access.allocation.mapping requested offset).2 hcovered)
    simpa [MemoryState.ResolvedAccess.cellAt?, hcovered, BackingRecord.cellAt?,
      ByteStore.InitializedAt] using hbacking
  · intro h backingOffset hcovered
    have horigin : access.allocation.origin ≤ backingOffset := by
      rw [ByteRange.covers_def] at hcovered
      change access.allocation.origin + requested.start ≤ backingOffset ∧ _ at hcovered
      omega
    have hlocal : requested.Covers (backingOffset - access.allocation.origin) := by
      apply (Coordinates.Mapping.span_covers access.allocation.mapping requested
        (backingOffset - access.allocation.origin)).1
      change (access.allocation.mapping.span requested).range.Covers backingOffset at hcovered
      simpa [AllocationRecord.mapping, Nat.add_sub_of_le horigin] using hcovered
    have hcell := h (backingOffset - access.allocation.origin) hlocal
    unfold MemoryState.InitializedAt at hcell
    rw [← access.cellAt?_eq_state hlocal] at hcell
    simpa [MemoryState.ResolvedAccess.cellAt?, hlocal, BackingRecord.cellAt?,
      ByteStore.InitializedAt, Nat.add_sub_of_le horigin] using hcell

/-- Cell agreement carries the initialization decision between two resolutions of
the same provenance and requested range. Stable metadata is handled separately by
the denial congruence theorem. -/
theorem MemoryState.ResolvedAccess.rangeInitialized_congr
    {a b : MemoryState} {provenance : Provenance} {requested : ByteRange}
    (accessA : a.ResolvedAccess provenance requested)
    (accessB : b.ResolvedAccess provenance requested) (hcells : a.AgreesOn b) :
    accessA.RangeInitialized ↔ accessB.RangeInitialized := by
  constructor
  · intro h
    apply accessB.rangeInitialized_iff_initializedAt.mpr
    intro offset hcovered
    have hinit := accessA.rangeInitialized_iff_initializedAt.mp h offset hcovered
    unfold MemoryState.InitializedAt at hinit ⊢
    rw [← hcells provenance.root offset]
    exact hinit
  · intro h
    apply accessA.rangeInitialized_iff_initializedAt.mpr
    intro offset hcovered
    have hinit := accessB.rangeInitialized_iff_initializedAt.mp h offset hcovered
    unfold MemoryState.InitializedAt at hinit ⊢
    rw [hcells provenance.root offset]
    exact hinit

/-- Local disjointness becomes backing-span disjointness when two resolutions use
the same allocation identity. `ByteRange.Disjoint.of_take` is the theorem that
keeps the writer's prefix disjoint. -/
theorem MemoryState.ResolvedAccess.prefix_span_disjoint_of_same_root
    {state : MemoryState} {writerProvenance queryProvenance : Provenance}
    {writerRange queryRange : ByteRange}
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (query : state.ResolvedAccess queryProvenance queryRange) (count : Nat)
    (hroot : writerProvenance.root = queryProvenance.root)
    (hdisjoint : writerRange.Disjoint queryRange) :
    (writer.prefix count).span.Disjoint query.span := by
  have hallocation : writer.allocation = query.allocation := by
    apply Option.some.inj
    exact writer.allocationLookup.symm.trans (hroot ▸ query.allocationLookup)
  unfold MemoryState.ResolvedAccess.span Coordinates.ResolvedRange.span
  change (writer.allocation.mapping.span (writerRange.take count)).Disjoint
    (query.allocation.mapping.span queryRange)
  rw [hallocation]
  exact (Coordinates.Mapping.span_disjoint_iff query.allocation.mapping
    (writerRange.take count) queryRange).2 ((hdisjoint.symm.of_take count).symm)

/-- Under the executable layout gate, distinct live allocations have disjoint
backing spans because their backing identities differ. -/
theorem MemoryState.ResolvedAccess.prefix_span_disjoint_of_ne
    {state : MemoryState} (hdedicated : state.DedicatedBackings)
    {writerProvenance queryProvenance : Provenance}
    {writerRange queryRange : ByteRange}
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (query : state.ResolvedAccess queryProvenance queryRange) (count : Nat)
    (hne : writerProvenance.root ≠ queryProvenance.root) :
    (writer.prefix count).span.Disjoint query.span := by
  left
  have hbacking := hdedicated.backing_ne_of_live_lookup
    writer.allocationLookup query.allocationLookup writer.allocationLive
      query.allocationLive hne
  change writer.allocation.backing ≠ query.allocation.backing
  exact hbacking

/--
Commit an access's written bytes to memory.

**The single path by which an access commits.** `Grass/Op/Step.lean`'s
`performAccess` and `applyAccess` below both go through this, so the framing laws
stated here are laws about the transition and not about a parallel implementation
that happens to agree. An earlier arrangement had the two writing memory
separately, which was a second source of truth for backing selection, and review
found it.

Not the single *write* primitive: that is `MemoryState.writeResolved`, which
`commitResolved` wraps and which `Grass/Memory/Shape.lean`'s `writeField` also calls
after resolving its field range, since a typed field store is not an access. An
earlier version of this paragraph said
"the single write path" flatly and review corrected it. What is true is narrower
and is the thing the laws need: every `AccessDescriptor` that commits, commits
here.

`none` means the access wrote nothing, which is not the same as writing zero
bytes: a read commits no write at all.
-/
def WrittenFits (d : AccessDescriptor) (written : Option ByteSeq) : Prop :=
  ∀ bytes, written = some bytes → bytes.length ≤ d.range.size

/-- Commit through the already prepared mapping. There is no second lookup and
no missing-backing fallback. -/
def MemoryState.commitResolved (state : MemoryState) (d : AccessDescriptor)
    (access : state.ResolvedAccess d.provenance d.range)
    (written : Option ByteSeq) (hfits : WrittenFits d written) : MemoryState :=
  match written with
  | Option.none => state
  | some bytes =>
      state.writeResolved access bytes d.producesInitialized (hfits bytes rfl)

/-- A commit changes no authority, whatever it writes. -/
@[simp] theorem grantEntries_commitResolved (state : MemoryState) (d : AccessDescriptor)
    (access : state.ResolvedAccess d.provenance d.range)
    (written : Option ByteSeq) (hfits : WrittenFits d written) :
    (state.commitResolved d access written hfits).grantEntries = state.grantEntries := by
  unfold MemoryState.commitResolved
  split
  · rfl
  · exact MemoryState.grantEntries_writeResolved _ _ _ _ _

/-- `dedicatedBackings_commitResolved` states that a resolved commit preserves the
temporary executable backing profile. -/
theorem dedicatedBackings_commitResolved (state : MemoryState) (d : AccessDescriptor)
    (access : state.ResolvedAccess d.provenance d.range)
    (written : Option ByteSeq) (hfits : WrittenFits d written)
    (hdedicated : state.DedicatedBackings) :
    (state.commitResolved d access written hfits).DedicatedBackings := by
  unfold MemoryState.commitResolved
  split
  · exact hdedicated
  · exact hdedicated.writeResolved _ _ _ _

/-- A resolved byte write changes no fact used by the executable backing-layout
gate. The biconditional is needed when carrying a denial in either direction. -/
@[simp] theorem dedicatedBackings_writeResolved_iff (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) :
    (state.writeResolved access bytes initializes fits).DedicatedBackings ↔
      state.DedicatedBackings := by
  unfold MemoryState.DedicatedBackings
  simp only [MemoryState.allocations_writeResolved,
    MemoryState.backingCapacity?_writeResolved]

@[simp] theorem commitResolved_of_eq_none (state : MemoryState) (d : AccessDescriptor)
    (access : state.ResolvedAccess d.provenance d.range)
    (written : Option ByteSeq) (hfits : WrittenFits d written)
    (h : written = none) : state.commitResolved d access written hfits = state := by
  subst written
  rfl

@[simp] theorem commitResolved_of_eq_some (state : MemoryState) (d : AccessDescriptor)
    (access : state.ResolvedAccess d.provenance d.range)
    (written : Option ByteSeq) (hfits : WrittenFits d written) (bytes : ByteSeq)
    (h : written = some bytes) :
    state.commitResolved d access written hfits =
      state.writeResolved access bytes d.producesInitialized (hfits bytes h) := by
  subst written
  rfl

@[simp] theorem metadataAt_commitResolved (state : MemoryState) (d : AccessDescriptor)
    (access : state.ResolvedAccess d.provenance d.range)
    (written : Option ByteSeq) (hfits : WrittenFits d written) (id : AllocId) :
    (state.commitResolved d access written hfits).MetadataAt id = state.MetadataAt id := by
  cases written with
  | none => rfl
  | some bytes =>
      exact MemoryState.metadataAt_writeResolved state access bytes
        d.producesInitialized (hfits bytes rfl) id

/-- `WrittenFits d written` bounds committed bytes by the range the access
declared. `Committed.writtenFits` is where the transition gets it; `applyAccess`
gets it by truncating. Without it a commit could write past the declared range
and every framing argument stated over `d.range` would be false. -/
def writtenBytes (d : AccessDescriptor) (writeData : ByteSeq) : Option ByteSeq :=
  if d.intent.writes then some (writeData.take d.range.size) else none

theorem writtenBytes_fits (d : AccessDescriptor) (writeData : ByteSeq) :
    WrittenFits d (writtenBytes d writeData) := by
  intro bytes h
  unfold writtenBytes at h
  split at h
  · cases h
    simpa only [List.length_take] using Nat.min_le_left d.range.size writeData.length
  · simp at h

/--
**A commit frames every cell the access did not declare.**

The law both write paths inherit. Stated over the *declared* range, which is what
a caller reads off a descriptor, and sound because `WrittenFits` bounds what was
actually written by it.
-/
theorem cellAt?_commitResolved_of_span_disjoint (state : MemoryState)
    (d : AccessDescriptor) (access : state.ResolvedAccess d.provenance d.range)
    {written : Option ByteSeq} (hfits : WrittenFits d written)
    {span : Coordinates.BackingSpan}
    (hdisjoint : ∀ bytes, written = some bytes →
      (access.prefix bytes.length).span.Disjoint span) (offset : Nat) :
    (state.commitResolved d access written hfits).cellAtBacking? span offset =
      state.cellAtBacking? span offset := by
  unfold MemoryState.commitResolved
  split
  · rfl
  · apply MemoryState.cellAtBacking?_writeResolved_of_span_disjoint
    exact hdisjoint _ rfl

/-- Under the executable dedicated-backing profile, a commit frames every
allocation-local cell outside the descriptor's declared footprint. -/
theorem cellAt?_commitResolved_of_untouched (state : MemoryState)
    (d : AccessDescriptor) (access : state.ResolvedAccess d.provenance d.range)
    {written : Option ByteSeq} (hfits : WrittenFits d written)
    (hdedicated : state.DedicatedBackings) {id : AllocId} {offset : Nat}
    (h : ¬ (d.provenance.root = id ∧ d.range.Covers offset)) :
    (state.commitResolved d access written hfits).cellAt? id offset =
      state.cellAt? id offset := by
  unfold MemoryState.commitResolved
  split
  · rfl
  · apply MemoryState.cellAt?_writeResolved_of_untouched
    · exact hdedicated
    · exact h

/--
Apply one access to memory.

Total: every descriptor and every state produce a result. Refusal returns the
state unchanged, which is `applyAccess_refused_preserves_state`.
-/
def applyAccess (state : MemoryState) (d : AccessDescriptor) (writeData : ByteSeq)
    (indeterminate : Nat → Byte) : AccessResult × MemoryState :=
  match prepareAccess state d with
  | .error class_ => (.refused class_, state)
  | .ok access =>
      ( { observed :=
            if d.intent.reads then some (observedBytes access indeterminate)
            else Option.none
          refusal := Option.none }
      , state.commitResolved d access (writtenBytes d writeData)
          (writtenBytes_fits d writeData) )

/-! ## The laws

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4 lists what the symbolic verifier consumes.
These are the ones about memory alone; the ones about events, obligations, and
the audit ledger are `Grass/Op/Step.lean`'s.

Framing is stated over cells rather than over states, deliberately. Two writes to
disjoint ranges leave the byte store's write history in different orders, so the
states are not equal and no amount of proving will make them equal. What is true
is that they agree at every offset, in byte *and* in initialization — the second
half matters because `denialOf` reads initialization, so a values-only agreement
would not carry the refusal decision. `docs/OLEAN_SHARDING.md` §1 asks for facts to cross the boundary as
exported theorems rather than as a representation consumers unfold, which is the
same discipline seen from the other side.
-/

/-- **A refused access preserves the state.** `applyAccess_refused_preserves_state`
is `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's first required law, and discharges
`docs/MEMORY_MODEL.md` §1's requirement that the check happen before anything
commits. -/
theorem applyAccess_refused_preserves_state (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {class_ : AuditViolationClass}
    (h : denialOf state d = some class_) :
    applyAccess state d writeData indeterminate = (.refused class_, state) := by
  unfold denialOf at h
  cases hp : prepareAccess state d with
  | error c =>
      simp only [hp] at h
      cases h
      simp [applyAccess, hp]
  | ok access => simp [hp] at h

/-- A refused access observes nothing. A refusal that still reported bytes would
let a denied read leak the storage it was denied. -/
theorem applyAccess_refused_observes_nothing (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {class_ : AuditViolationClass}
    (h : denialOf state d = some class_) :
    (applyAccess state d writeData indeterminate).1.observed = Option.none := by
  rw [applyAccess_refused_preserves_state state d writeData indeterminate h]
  rfl

/--
What `applyAccess` leaves in memory, in one equation.

Every framing law below goes through this rather than through `applyAccess`'s
branches, so a change to the branch structure moves one proof rather than all of
them.
-/
theorem applyAccess_state (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) :
    (applyAccess state d writeData indeterminate).2 =
      match prepareAccess state d with
      | .error _ => state
      | .ok access =>
          state.commitResolved d access (writtenBytes d writeData)
            (writtenBytes_fits d writeData) := by
  unfold applyAccess
  split <;> rfl

/-- A read-only access leaves memory untouched. -/
theorem applyAccess_read_preserves_state (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) (h : d.intent.writes = false) :
    (applyAccess state d writeData indeterminate).2 = state := by
  have hwritten : writtenBytes d writeData = none := by simp [writtenBytes, h]
  rw [applyAccess_state]
  cases prepareAccess state d with
  | error _ => rfl
  | ok access => exact commitResolved_of_eq_none state d access _ _ hwritten

/-- **An access frames every other allocation in executable states.** A successful
preparation establishes `DedicatedBackings`; a state outside that profile is
refused unchanged. -/
theorem applyAccess_frames_other_allocation (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {other : AllocId}
    (hne : other ≠ d.provenance.root) (offset : Nat) :
    (applyAccess state d writeData indeterminate).2.byteAt? other offset =
      state.byteAt? other offset := by
  unfold MemoryState.byteAt?
  unfold applyAccess
  cases hp : prepareAccess state d with
  | error _ => rfl
  | ok access =>
      rw [cellAt?_commitResolved_of_untouched state d access
        (writtenBytes_fits d writeData) (dedicatedBackings_of_prepareAccess hp)]
      exact fun h => hne h.1.symm

/-- **An access frames every range in its own allocation that it did not write.**
The pointwise form; `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's "reads and writes to
disjoint ranges commute and frame", framing half. -/
theorem applyAccess_frames_uncovered_offset (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {offset : Nat}
    (hout : ¬ d.range.Covers offset) :
    (applyAccess state d writeData indeterminate).2.byteAt? d.provenance.root offset =
      state.byteAt? d.provenance.root offset := by
  unfold MemoryState.byteAt?
  unfold applyAccess
  cases hp : prepareAccess state d with
  | error _ => rfl
  | ok access =>
      rw [cellAt?_commitResolved_of_untouched state d access
        (writtenBytes_fits d writeData) (dedicatedBackings_of_prepareAccess hp)]
      exact fun h => hout h.2

/-- The range-level framing law, which is the one a disjointness argument states:
an access confined to `d.range` leaves every byte of a disjoint range as it was. -/
theorem applyAccess_frames_disjoint_range (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {other : ByteRange}
    (hd : d.range.Disjoint other) {offset : Nat} (hcov : other.Covers offset) :
    (applyAccess state d writeData indeterminate).2.byteAt? d.provenance.root offset =
      state.byteAt? d.provenance.root offset := by
  refine applyAccess_frames_uncovered_offset state d writeData indeterminate ?_
  exact fun hin => hd.not_covers hin hcov

/-- The result branch exposes the same prepared access used by observation and
commit; no consumer needs to resolve the descriptor again. -/
theorem applyAccess_result (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) :
    (applyAccess state d writeData indeterminate).1 =
      match prepareAccess state d with
      | .error class_ => .refused class_
      | .ok access =>
          { observed := if d.intent.reads then
              some (observedBytes access indeterminate) else none
            refusal := none } := by
  unfold applyAccess
  cases prepareAccess state d <;> rfl

/-- Resolved snapshots with the same requested cells produce the same observed
byte sequence. -/
theorem observedBytes_congr {a b : MemoryState} {d : AccessDescriptor}
    (accessA : a.ResolvedAccess d.provenance d.range)
    (accessB : b.ResolvedAccess d.provenance d.range) (indeterminate : Nat → Byte)
    (h : ∀ offset, offset < d.range.size →
      accessA.byteAt? (d.range.start + offset) =
        accessB.byteAt? (d.range.start + offset)) :
    observedBytes accessA indeterminate = observedBytes accessB indeterminate := by
  unfold observedBytes
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [h i hi]


/-! ### Denial is framed too

Byte framing is only half of commutation. The backing-span laws below also carry
stable allocation/backing metadata, initialization outside the written prefix,
and `DedicatedBackings`, so a later access is prepared against the same mapping
and capacity rather than resolved independently.
-/

/-- Once both states have resolved the same descriptor, stable access metadata,
agreement on initialization, and agreement on the global executable-layout gate
make their remaining denial decisions identical. -/
theorem denialOf_congr_of_resolved_init {a b : MemoryState} {d : AccessDescriptor}
    (accessA : a.ResolvedAccess d.provenance d.range)
    (accessB : b.ResolvedAccess d.provenance d.range)
    (hmeta : a.MetadataAt d.provenance.root = b.MetadataAt d.provenance.root)
    (hinitialized : accessA.RangeInitialized ↔ accessB.RangeInitialized)
    (hdedicated : a.DedicatedBackings ↔ b.DedicatedBackings) :
    denialOf a d = denialOf b d := by
  have hrecordMeta : accessA.allocation.metadata = accessB.allocation.metadata := by
    unfold MemoryState.MetadataAt at hmeta
    rw [accessA.allocationLookup, accessB.allocationLookup] at hmeta
    exact congrArg MemoryState.AccessMetadata.allocation (Option.some.inj hmeta)
  have hextent : accessA.allocation.extent = accessB.allocation.extent :=
    congrArg AllocationRecord.Metadata.extent hrecordMeta
  have hpermission : accessA.allocation.permission = accessB.allocation.permission :=
    congrArg AllocationRecord.Metadata.permission hrecordMeta
  have hbase : accessA.allocation.base = accessB.allocation.base :=
    congrArg AllocationRecord.Metadata.base hrecordMeta
  unfold denialOf prepareAccess
  rw [MemoryState.resolveAccess?_eq_ok accessA, MemoryState.resolveAccess?_eq_ok accessB]
  by_cases hda : a.DedicatedBackings
  <;> by_cases hdb : b.DedicatedBackings
  <;> by_cases hwrap : accessB.allocation.base.any
        (fun base => !decide (FitsAllocation base accessB.allocation.extent.stop)) = true
  <;> by_cases haddress : accessB.allocation.base.any
        (fun base => d.address != Address.numeric (addressOf base d.range.start)) = true
  <;> by_cases hgrants : accessB.allocation.permission.Grants d.requiredPermission
  <;> by_cases hpermits : accessB.allocation.permission.Permits d.intent
  <;> by_cases hinit : d.initialization = .allBytesInitialized ∧
        ¬ accessB.RangeInitialized
  <;> simp_all
  all_goals
    have hnotinit : ¬ (d.initialization = .allBytesInitialized ∧
        ¬ accessB.RangeInitialized) := by
      intro h
      exact h.2 (hinit h.1)
    simp [hnotinit]

/-- Checked-cell agreement supplies the initialization premise of
`denialOf_congr_of_resolved_init`. `denialOf_congr_of_resolved` keeps an explicit
`DedicatedBackings` equivalence because `MetadataAt` describes only one allocation. -/
theorem denialOf_congr_of_resolved {a b : MemoryState} {d : AccessDescriptor}
    (accessA : a.ResolvedAccess d.provenance d.range)
    (accessB : b.ResolvedAccess d.provenance d.range)
    (hmeta : a.MetadataAt d.provenance.root = b.MetadataAt d.provenance.root)
    (hcells : a.AgreesOn b)
    (hdedicated : a.DedicatedBackings ↔ b.DedicatedBackings) :
    denialOf a d = denialOf b d :=
  denialOf_congr_of_resolved_init accessA accessB hmeta
    (accessA.rangeInitialized_congr accessB hcells) hdedicated

/-- States agreeing on stable metadata and every checked cell decide an access the
same way, provided they also agree on the global executable-layout gate. The latter
is separate because metadata at `d`'s root cannot describe unrelated bindings. -/
theorem denialOf_congr_of_agrees {a b : MemoryState} {d : AccessDescriptor}
    (hmeta : a.MetadataAt d.provenance.root = b.MetadataAt d.provenance.root)
    (hcells : a.AgreesOn b)
    (hdedicated : a.DedicatedBackings ↔ b.DedicatedBackings) :
    denialOf a d = denialOf b d := by
  have hclassification := MemoryState.resolveClassification_congr_metadata
    (provenance := d.provenance) (requested := d.range) hmeta
  cases ha : a.resolveAccess? d.provenance d.range with
  | error failureA =>
      cases hb : b.resolveAccess? d.provenance d.range with
      | error failureB =>
          have hf : failureA = failureB := by
            simpa [MemoryState.resolveClassification, ha, hb] using hclassification
          subst failureB
          simp [denialOf, prepareAccess, ha, hb]
      | ok accessB =>
          simp [MemoryState.resolveClassification, ha, hb] at hclassification
  | ok accessA =>
      cases hb : b.resolveAccess? d.provenance d.range with
      | error failureB =>
          simp [MemoryState.resolveClassification, ha, hb] at hclassification
      | ok accessB =>
          exact denialOf_congr_of_resolved accessA accessB hmeta hcells hdedicated

/-- A backing-span-disjoint resolved write preserves every denial class for `d`.
Resolver failures are carried by stable metadata; for a successful resolution,
the disjoint backing spans carry the initialization clause as well. -/
theorem denialOf_writeResolved_of_span_disjoint (state : MemoryState)
    (d : AccessDescriptor) {writerProvenance : Provenance}
    {writerRange : ByteRange}
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ writerRange.size)
    (hdisjoint : ∀ query : state.ResolvedAccess d.provenance d.range,
      (writer.prefix bytes.length).span.Disjoint query.span) :
    denialOf (state.writeResolved writer bytes initializes fits) d = denialOf state d := by
  let after := state.writeResolved writer bytes initializes fits
  change denialOf after d = denialOf state d
  have hmeta : after.MetadataAt d.provenance.root = state.MetadataAt d.provenance.root := by
    exact MemoryState.metadataAt_writeResolved state writer bytes initializes fits _
  have hgate : after.DedicatedBackings ↔ state.DedicatedBackings := by
    exact dedicatedBackings_writeResolved_iff state writer bytes initializes fits
  have hclassification := MemoryState.resolveClassification_congr_metadata
    (requested := d.range) hmeta
  cases hquery : state.resolveAccess? d.provenance d.range with
  | error failure =>
      cases hafter : after.resolveAccess? d.provenance d.range with
      | error afterFailure =>
          have hf : afterFailure = failure := by
            simpa [MemoryState.resolveClassification, hafter, hquery] using hclassification
          subst afterFailure
          simp [denialOf, prepareAccess, hafter, hquery]
      | ok afterAccess =>
          simp [MemoryState.resolveClassification, hafter, hquery] at hclassification
  | ok query =>
      let afterQuery := query.afterWrite writer bytes initializes fits
      exact denialOf_congr_of_resolved_init afterQuery query hmeta
        (MemoryState.rangeInitialized_afterWrite_iff_of_span_disjoint
          query writer bytes initializes fits (hdisjoint query)) hgate

/-- A successfully prepared descriptor remains successfully prepared after a
backing-span-disjoint write, with the resolver evidence transported through that
exact write. -/
theorem prepareAccess_writeResolved_of_span_disjoint (state : MemoryState)
    (d : AccessDescriptor) {writerProvenance : Provenance}
    {writerRange : ByteRange}
    (query : state.ResolvedAccess d.provenance d.range)
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ writerRange.size)
    (hprepared : prepareAccess state d = .ok query)
    (hdisjoint : (writer.prefix bytes.length).span.Disjoint query.span) :
    prepareAccess (state.writeResolved writer bytes initializes fits) d =
      .ok (query.afterWrite writer bytes initializes fits) := by
  have hdedicated : state.DedicatedBackings :=
    dedicatedBackings_of_prepareAccess hprepared
  have hafterDedicated :
      (state.writeResolved writer bytes initializes fits).DedicatedBackings :=
    hdedicated.writeResolved writer bytes initializes fits
  have hinitialized := MemoryState.rangeInitialized_afterWrite_iff_of_span_disjoint
    query writer bytes initializes fits hdisjoint
  unfold prepareAccess at hprepared ⊢
  rw [MemoryState.resolveAccess?_eq_ok query] at hprepared
  rw [MemoryState.resolveAccess?_eq_ok (query.afterWrite writer bytes initializes fits)]
  simp only at hprepared ⊢
  simp only [hdedicated, not_true_eq_false, if_false] at hprepared
  simp only [hafterDedicated, not_true_eq_false, if_false]
  simp only [MemoryState.ResolvedAccess.afterWrite_allocation]
  repeat' split at hprepared <;> simp_all

/-- `denialOf_commitResolved_of_span_disjoint` preserves a backing-span-disjoint
descriptor's denial and requests disjointness only in the branch that writes. -/
theorem denialOf_commitResolved_of_span_disjoint (state : MemoryState)
    (writerDescriptor queryDescriptor : AccessDescriptor)
    (writer : state.ResolvedAccess writerDescriptor.provenance writerDescriptor.range)
    (written : Option ByteSeq) (fits : WrittenFits writerDescriptor written)
    (hdisjoint : ∀ bytes, written = some bytes →
      ∀ query : state.ResolvedAccess queryDescriptor.provenance queryDescriptor.range,
        (writer.prefix bytes.length).span.Disjoint query.span) :
    denialOf (state.commitResolved writerDescriptor writer written fits) queryDescriptor =
      denialOf state queryDescriptor := by
  cases written with
  | none => rfl
  | some bytes =>
      exact denialOf_writeResolved_of_span_disjoint state queryDescriptor writer bytes
        writerDescriptor.producesInitialized (fits bytes rfl) (hdisjoint bytes rfl)

/-- `denialOf_applyAccess_of_disjoint` preserves the denial decision for a disjoint
range in the same allocation by comparing the translated backing spans. -/
theorem denialOf_applyAccess_of_disjoint (state : MemoryState)
    (dA dB : AccessDescriptor) (writeData : ByteSeq) (indeterminate : Nat → Byte)
    (hroot : dA.provenance.root = dB.provenance.root)
    (hdisjoint : dA.range.Disjoint dB.range) :
    denialOf (applyAccess state dA writeData indeterminate).2 dB = denialOf state dB := by
  rw [applyAccess_state]
  cases hprepared : prepareAccess state dA with
  | error _ => simp only
  | ok writer =>
      simp only
      apply denialOf_commitResolved_of_span_disjoint
      intro bytes _ query
      exact writer.prefix_span_disjoint_of_same_root query bytes.length hroot hdisjoint

/-- `denialOf_applyAccess_of_other_allocation` preserves the denial decision across
distinct allocations. `dedicatedBackings_of_prepareAccess` supplies the fact used
to separate their backing identities. -/
theorem denialOf_applyAccess_of_other_allocation (state : MemoryState)
    (dA dB : AccessDescriptor) (writeData : ByteSeq) (indeterminate : Nat → Byte)
    (hne : dB.provenance.root ≠ dA.provenance.root) :
    denialOf (applyAccess state dA writeData indeterminate).2 dB = denialOf state dB := by
  rw [applyAccess_state]
  cases hprepared : prepareAccess state dA with
  | error _ => simp only
  | ok writer =>
      simp only
      apply denialOf_commitResolved_of_span_disjoint
      intro bytes _ query
      exact writer.prefix_span_disjoint_of_ne
        (dedicatedBackings_of_prepareAccess hprepared) query bytes.length hne.symm

/-- Two successfully prepared accesses with disjoint backing-coordinate prefixes commute
observationally. This is the core state theorem; the source-coordinate wrappers
below derive its span premise from either local disjointness or distinct live
allocation identities. -/
theorem applyAccess_comm_of_prepared (state : MemoryState)
    (dA dB : AccessDescriptor) (writeA writeB : ByteSeq)
    (indetA indetB : Nat → Byte)
    (accessA : state.ResolvedAccess dA.provenance dA.range)
    (accessB : state.ResolvedAccess dB.provenance dB.range)
    (hpreparedA : prepareAccess state dA = .ok accessA)
    (hpreparedB : prepareAccess state dB = .ok accessB)
    (hdisjointA : ∀ countA,
      (accessA.prefix countA).span.Disjoint accessB.span)
    (hdisjointB : ∀ countB,
      (accessB.prefix countB).span.Disjoint accessA.span)
    (hdisjointWrites : ∀ countA countB,
      (accessA.prefix countA).span.Disjoint (accessB.prefix countB).span) :
    (applyAccess (applyAccess state dA writeA indetA).2 dB writeB indetB).2.AgreesOn
      (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).2 := by
  have hstateA : (applyAccess state dA writeA indetA).2 =
      state.commitResolved dA accessA (writtenBytes dA writeA)
        (writtenBytes_fits dA writeA) := by
    rw [applyAccess_state, hpreparedA]
  have hstateB : (applyAccess state dB writeB indetB).2 =
      state.commitResolved dB accessB (writtenBytes dB writeB)
        (writtenBytes_fits dB writeB) := by
    rw [applyAccess_state, hpreparedB]
  cases hwrittenA : writtenBytes dA writeA with
  | none =>
      have hstateA' : (applyAccess state dA writeA indetA).2 = state := by
        rw [hstateA, commitResolved_of_eq_none state dA accessA _ _ hwrittenA]
      cases hwrittenB : writtenBytes dB writeB with
      | none =>
          have hstateB' : (applyAccess state dB writeB indetB).2 = state := by
            rw [hstateB, commitResolved_of_eq_none state dB accessB _ _ hwrittenB]
          simpa only [hstateA', hstateB'] using MemoryState.AgreesOn.refl state
      | some bytesB =>
          have hstateB' : (applyAccess state dB writeB indetB).2 =
              state.writeResolved accessB bytesB dB.producesInitialized
                (writtenBytes_fits dB writeB bytesB hwrittenB) := by
            rw [hstateB, commitResolved_of_eq_some state dB accessB _ _ _ hwrittenB]
          have hpreparedAfterB := prepareAccess_writeResolved_of_span_disjoint
            state dA accessA accessB bytesB dB.producesInitialized
              (writtenBytes_fits dB writeB bytesB hwrittenB) hpreparedA
              (hdisjointB bytesB.length)
          simp only [hstateA', hstateB']
          rw [applyAccess_state, hpreparedAfterB]
          simp only
          rw [commitResolved_of_eq_none _ dA _ _ _ hwrittenA]
          exact MemoryState.AgreesOn.refl _
  | some bytesA =>
      have hstateA' : (applyAccess state dA writeA indetA).2 =
          state.writeResolved accessA bytesA dA.producesInitialized
            (writtenBytes_fits dA writeA bytesA hwrittenA) := by
        rw [hstateA, commitResolved_of_eq_some state dA accessA _ _ _ hwrittenA]
      cases hwrittenB : writtenBytes dB writeB with
      | none =>
          have hstateB' : (applyAccess state dB writeB indetB).2 = state := by
            rw [hstateB, commitResolved_of_eq_none state dB accessB _ _ hwrittenB]
          have hpreparedAfterA := prepareAccess_writeResolved_of_span_disjoint
            state dB accessB accessA bytesA dA.producesInitialized
              (writtenBytes_fits dA writeA bytesA hwrittenA) hpreparedB
              (hdisjointA bytesA.length)
          simp only [hstateA', hstateB']
          rw [applyAccess_state, hpreparedAfterA]
          simp only
          rw [commitResolved_of_eq_none _ dB _ _ _ hwrittenB]
          exact MemoryState.AgreesOn.refl _
      | some bytesB =>
          have hstateB' : (applyAccess state dB writeB indetB).2 =
              state.writeResolved accessB bytesB dB.producesInitialized
                (writtenBytes_fits dB writeB bytesB hwrittenB) := by
            rw [hstateB, commitResolved_of_eq_some state dB accessB _ _ _ hwrittenB]
          have hpreparedAfterA := prepareAccess_writeResolved_of_span_disjoint
            state dB accessB accessA bytesA dA.producesInitialized
              (writtenBytes_fits dA writeA bytesA hwrittenA) hpreparedB
              (hdisjointA bytesA.length)
          have hpreparedAfterB := prepareAccess_writeResolved_of_span_disjoint
            state dA accessA accessB bytesB dB.producesInitialized
              (writtenBytes_fits dB writeB bytesB hwrittenB) hpreparedA
              (hdisjointB bytesB.length)
          simp only [hstateA', hstateB']
          rw [applyAccess_state, hpreparedAfterA]
          simp only
          rw [commitResolved_of_eq_some _ dB _ _ _ _ hwrittenB]
          rw [applyAccess_state, hpreparedAfterB]
          simp only
          rw [commitResolved_of_eq_some _ dA _ _ _ _ hwrittenA]
          exact MemoryState.writeResolved_comm state accessA accessB bytesA bytesB
            dA.producesInitialized dB.producesInitialized
            (writtenBytes_fits dA writeA bytesA hwrittenA)
            (writtenBytes_fits dB writeB bytesB hwrittenB)
            (hdisjointWrites bytesA.length bytesB.length)

/-- **Accesses to disjoint ranges in one allocation commute**, in checked cells
and initialization. Refused branches preserve state; when both prepare, local
disjointness is translated through their one shared mapping. -/
theorem applyAccess_comm (state : MemoryState) (dA dB : AccessDescriptor)
    (writeA writeB : ByteSeq) (indetA indetB : Nat → Byte)
    (hroot : dA.provenance.root = dB.provenance.root)
    (hdisjoint : dA.range.Disjoint dB.range) :
    (applyAccess (applyAccess state dA writeA indetA).2 dB writeB indetB).2.AgreesOn
      (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).2 := by
  cases hdenA : denialOf state dA with
  | some classA =>
      have hstableA := denialOf_applyAccess_of_disjoint state dB dA writeB indetB
        hroot.symm hdisjoint.symm
      have hdenAfterA : denialOf (applyAccess state dB writeB indetB).2 dA =
          some classA := by rw [hstableA, hdenA]
      rw [applyAccess_refused_preserves_state state dA writeA indetA hdenA,
        applyAccess_refused_preserves_state _ dA writeA indetA hdenAfterA]
      exact MemoryState.AgreesOn.refl _
  | none =>
      cases hdenB : denialOf state dB with
      | some classB =>
          have hstableB := denialOf_applyAccess_of_disjoint state dA dB writeA indetA
            hroot hdisjoint
          have hdenAfterB : denialOf (applyAccess state dA writeA indetA).2 dB =
              some classB := by rw [hstableB, hdenB]
          rw [applyAccess_refused_preserves_state _ dB writeB indetB hdenAfterB,
            applyAccess_refused_preserves_state state dB writeB indetB hdenB]
          exact MemoryState.AgreesOn.refl _
      | none =>
          obtain ⟨accessA, hpreparedA⟩ := (denialOf_eq_none_iff state dA).mp hdenA
          obtain ⟨accessB, hpreparedB⟩ := (denialOf_eq_none_iff state dB).mp hdenB
          apply applyAccess_comm_of_prepared state dA dB writeA writeB indetA indetB
            accessA accessB hpreparedA hpreparedB
          · intro countA
            exact accessA.prefix_span_disjoint_of_same_root accessB countA
              hroot hdisjoint
          · intro countB
            exact accessB.prefix_span_disjoint_of_same_root accessA countB
              hroot.symm hdisjoint.symm
          · intro countA countB
            exact accessA.prefix_span_disjoint_of_same_root (accessB.prefix countB)
              countA hroot (hdisjoint.of_take countB)

/-- **Accesses in distinct live allocations commute** under the executable
dedicated-backing profile established by either successful preparation. -/
theorem applyAccess_comm_of_other_allocation (state : MemoryState)
    (dA dB : AccessDescriptor) (writeA writeB : ByteSeq)
    (indetA indetB : Nat → Byte)
    (hne : dA.provenance.root ≠ dB.provenance.root) :
    (applyAccess (applyAccess state dA writeA indetA).2 dB writeB indetB).2.AgreesOn
      (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).2 := by
  cases hdenA : denialOf state dA with
  | some classA =>
      have hstableA := denialOf_applyAccess_of_other_allocation
        state dB dA writeB indetB hne
      have hdenAfterA : denialOf (applyAccess state dB writeB indetB).2 dA =
          some classA := by rw [hstableA, hdenA]
      rw [applyAccess_refused_preserves_state state dA writeA indetA hdenA,
        applyAccess_refused_preserves_state _ dA writeA indetA hdenAfterA]
      exact MemoryState.AgreesOn.refl _
  | none =>
      cases hdenB : denialOf state dB with
      | some classB =>
          have hstableB := denialOf_applyAccess_of_other_allocation
            state dA dB writeA indetA hne.symm
          have hdenAfterB : denialOf (applyAccess state dA writeA indetA).2 dB =
              some classB := by rw [hstableB, hdenB]
          rw [applyAccess_refused_preserves_state _ dB writeB indetB hdenAfterB,
            applyAccess_refused_preserves_state state dB writeB indetB hdenB]
          exact MemoryState.AgreesOn.refl _
      | none =>
          obtain ⟨accessA, hpreparedA⟩ := (denialOf_eq_none_iff state dA).mp hdenA
          obtain ⟨accessB, hpreparedB⟩ := (denialOf_eq_none_iff state dB).mp hdenB
          have hdedicated := dedicatedBackings_of_prepareAccess hpreparedA
          apply applyAccess_comm_of_prepared state dA dB writeA writeB indetA indetB
            accessA accessB hpreparedA hpreparedB
          · intro countA
            exact accessA.prefix_span_disjoint_of_ne hdedicated accessB countA hne
          · intro countB
            exact accessB.prefix_span_disjoint_of_ne hdedicated accessA countB hne.symm
          · intro countA countB
            exact accessA.prefix_span_disjoint_of_ne hdedicated
              (accessB.prefix countB) countA hne

/-- Equal denial decisions and byte agreement over the descriptor's range give
the access the same result. Resolution remains checked independently in each
state; its successful evidence is used only to read the agreed cells. -/
theorem applyAccess_result_congr {a b : MemoryState} (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte)
    (hdenial : denialOf a d = denialOf b d)
    (hbytes : ∀ offset, d.range.Covers offset →
      a.byteAt? d.provenance.root offset = b.byteAt? d.provenance.root offset) :
    (applyAccess a d writeData indeterminate).1 =
      (applyAccess b d writeData indeterminate).1 := by
  cases hda : denialOf a d with
  | none =>
      have hdb : denialOf b d = none := by rw [← hdenial, hda]
      obtain ⟨accessA, hpreparedA⟩ := (denialOf_eq_none_iff a d).mp hda
      obtain ⟨accessB, hpreparedB⟩ := (denialOf_eq_none_iff b d).mp hdb
      have hobserved : observedBytes accessA indeterminate =
          observedBytes accessB indeterminate := by
        apply observedBytes_congr
        intro offset hoffset
        have hcovered : d.range.Covers (d.range.start + offset) :=
          ByteRange.covers_of (Nat.le_add_right _ _) (by omega)
        rw [accessA.byteAt?_eq_state hcovered, accessB.byteAt?_eq_state hcovered]
        exact hbytes _ hcovered
      rw [applyAccess_result, applyAccess_result, hpreparedA, hpreparedB]
      simp only
      rw [hobserved]
  | some class_ =>
      have hdb : denialOf b d = some class_ := by rw [← hdenial, hda]
      rw [applyAccess_refused_preserves_state a d writeData indeterminate hda,
        applyAccess_refused_preserves_state b d writeData indeterminate hdb]

/-- A descriptor produces the same result before or after an access to a
disjoint range in the same allocation. -/
theorem applyAccess_result_comm (state : MemoryState) (dA dB : AccessDescriptor)
    (writeA writeB : ByteSeq) (indetA indetB : Nat → Byte)
    (hroot : dA.provenance.root = dB.provenance.root)
    (hdisjoint : dA.range.Disjoint dB.range) :
    (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).1 =
      (applyAccess state dA writeA indetA).1 := by
  apply applyAccess_result_congr
  · exact denialOf_applyAccess_of_disjoint state dB dA writeB indetB
      hroot.symm hdisjoint.symm
  · intro offset hcovered
    have hframe := applyAccess_frames_disjoint_range state dB writeB indetB
      hdisjoint.symm hcovered
    simpa [hroot] using hframe

/-- The same result stability holds across distinct allocation identities. -/
theorem applyAccess_result_comm_of_other_allocation (state : MemoryState)
    (dA dB : AccessDescriptor) (writeA writeB : ByteSeq)
    (indetA indetB : Nat → Byte)
    (hne : dA.provenance.root ≠ dB.provenance.root) :
    (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).1 =
      (applyAccess state dA writeA indetA).1 := by
  apply applyAccess_result_congr
  · exact denialOf_applyAccess_of_other_allocation state dB dA writeB indetB hne
  · intro offset _
    exact applyAccess_frames_other_allocation state dB writeB indetB hne offset

/-! ## Straight-line blocks

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's exit criterion is that the framing set
suffices to discharge a straight-line Spike 1 block *without a bespoke local
lemma*. A block is a list of accesses run in order, and the law it needs is that
a byte no step touched is the byte it was before the block began.

The hypothesis is stated over each step's declared `range` rather than over the
bytes it actually wrote. That is the weaker fact and the useful one: a caller
reasoning about a block knows the ranges from the descriptors, and does not know
how much data each store carried. `applyAccess` only ever writes inside the
declared range, so the stronger hypothesis would buy nothing and cost every
caller an extra obligation.
-/

/-- **An access moves no allocation or backing-capacity metadata.** It changes only
the selected backing's byte store, which is what makes a later access resolve the
same mapping and capacity. -/
theorem applyAccess_preserves_metadata (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) (other : AllocId) :
    (applyAccess state d writeData indeterminate).2.MetadataAt other =
      state.MetadataAt other := by
  rw [applyAccess_state]
  cases prepareAccess state d with
  | error _ => rfl
  | ok access => exact metadataAt_commitResolved state d access _ _ other

/--
**§10's preservation item, as far as this layer can state it.**

`docs/MEMORY_MODEL.md` §10 asks that "range, provenance, and initialization are
preserved by admitted steps". The third field of `RequiredProofPackage` to stop being a
bare `Prop`; `MemoryState.LoanMapLaws` has the argument for why that matters.

**It is the half about `applyAccess`, and the docstring says so because the type
cannot.** `Grass/Op/Step.lean` imports `Grass/Memory/Profile.lean`, so the package
cannot mention the transition at all — that is a layering fact, not a missing theorem,
and `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records what moving it would cost. A
partial statement is still worth more than a `Prop` a profile names: this one has
content, and a profile cannot choose it.

The conjuncts say: refusal changes nothing; a non-writing access changes nothing;
stable allocation/backing metadata does not move; every checked cell outside the
declared footprint is framed in both value and initialization; and the temporary
dedicated-backing execution invariant is preserved.
-/
def PreservationLaws : Prop :=
  (∀ (state : MemoryState) (d : AccessDescriptor) (writeData : ByteSeq)
      (indeterminate : Nat → Byte) (class_ : AuditViolationClass),
      denialOf state d = some class_ →
      applyAccess state d writeData indeterminate = (.refused class_, state)) ∧
  (∀ (state : MemoryState) (d : AccessDescriptor) (writeData : ByteSeq)
      (indeterminate : Nat → Byte),
      d.intent.writes = false →
      (applyAccess state d writeData indeterminate).2 = state) ∧
  (∀ (state : MemoryState) (d : AccessDescriptor) (writeData : ByteSeq)
      (indeterminate : Nat → Byte) (other : AllocId),
      (applyAccess state d writeData indeterminate).2.MetadataAt other =
        state.MetadataAt other) ∧
  (∀ (state : MemoryState) (d : AccessDescriptor) (writeData : ByteSeq)
      (indeterminate : Nat → Byte) (id : AllocId) (offset : Nat),
      ¬ (d.provenance.root = id ∧ d.range.Covers offset) →
        (applyAccess state d writeData indeterminate).2.cellAt? id offset =
          state.cellAt? id offset) ∧
  (∀ (state : MemoryState) (d : AccessDescriptor) (writeData : ByteSeq)
      (indeterminate : Nat → Byte), state.DedicatedBackings →
      (applyAccess state d writeData indeterminate).2.DedicatedBackings)

/-- **The preservation laws hold**, including stable backing metadata and the
temporary applicability invariant. -/
theorem preservationLaws : PreservationLaws :=
  ⟨fun state d writeData ind _ h =>
     applyAccess_refused_preserves_state state d writeData ind h,
   fun state d writeData ind h => applyAccess_read_preserves_state state d writeData ind h,
   fun state d writeData ind other =>
     applyAccess_preserves_metadata state d writeData ind other,
   fun state d writeData ind id offset hout => by
     unfold applyAccess
     cases hp : prepareAccess state d with
     | error _ => rfl
     | ok access =>
         exact cellAt?_commitResolved_of_untouched state d access
           (writtenBytes_fits d writeData) (dedicatedBackings_of_prepareAccess hp) hout,
   fun state d writeData ind hdedicated => by
     unfold applyAccess
     cases hp : prepareAccess state d with
     | error _ => exact hdedicated
     | ok access =>
         exact dedicatedBackings_commitResolved state d access
           (writtenBytes d writeData) (writtenBytes_fits d writeData) hdedicated⟩

/-- Run a block of accesses in order, threading the state. -/
def runBlock (state : MemoryState) (indeterminate : Nat → Byte) :
    List (AccessDescriptor × ByteSeq) → List AccessResult × MemoryState
  | [] => ([], state)
  | (d, writeData) :: rest =>
      let step := applyAccess state d writeData indeterminate
      let after := runBlock step.2 indeterminate rest
      (step.1 :: after.1, after.2)

/--
**What memory looks like afterwards does not depend on what an indeterminate read
would have observed.**

`indeterminate` answers reads of bytes the store has no value for. This says that
answer stays in the observation and never reaches memory — so a profile choosing
differently changes what a program *sees*, never what it *leaves behind*. Without
it every downstream fact about a block's final state would be parameterized by a
choice that provably does not affect it.
-/
theorem applyAccess_state_indep (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (ind ind' : Nat → Byte) :
    (applyAccess state d writeData ind).2 = (applyAccess state d writeData ind').2 := by
  rw [applyAccess_state, applyAccess_state]

/-- `step.Touches id offset` holds when this step's declared range covers that
byte of that allocation. Everything else the step provably leaves alone. -/
def Touches (step : AccessDescriptor × ByteSeq) (id : AllocId) (offset : Nat) : Prop :=
  step.1.provenance.root = id ∧ step.1.range.Covers offset

instance (step : AccessDescriptor × ByteSeq) (id : AllocId) (offset : Nat) :
    Decidable (Touches step id offset) := inferInstanceAs (Decidable (_ ∧ _))

/-- **One access frames every cell it does not touch**, byte and initialization
together. The cell-level form the block law is built from. -/
theorem cellAt?_applyAccess_of_untouched (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {id : AllocId} {offset : Nat}
    (h : ¬ Touches (d, writeData) id offset) :
    (applyAccess state d writeData indeterminate).2.cellAt? id offset =
      state.cellAt? id offset := by
  unfold applyAccess
  cases hp : prepareAccess state d with
  | error _ => rfl
  | ok access =>
      exact cellAt?_commitResolved_of_untouched state d access
        (writtenBytes_fits d writeData) (dedicatedBackings_of_prepareAccess hp) h

/--
**A straight-line block frames every cell no step of it touches.**

The exit criterion's lemma. A caller discharges a block by checking each step's
declared range against the bytes it cares about — which is decidable, and is what
`Touches` is for — and needs nothing else about what the block did.
-/
theorem cellAt?_runBlock_of_untouched (indeterminate : Nat → Byte) :
    ∀ (block : List (AccessDescriptor × ByteSeq)) (state : MemoryState) {id : AllocId}
      {offset : Nat}, (∀ step ∈ block, ¬ Touches step id offset) →
      (runBlock state indeterminate block).2.cellAt? id offset = state.cellAt? id offset
  | [], _, _, _, _ => rfl
  | (d, writeData) :: rest, state, id, offset, hall => by
    rw [runBlock,
      cellAt?_runBlock_of_untouched indeterminate rest _
        (fun step hstep => hall step (List.mem_cons_of_mem _ hstep)),
      cellAt?_applyAccess_of_untouched state d writeData indeterminate
        (hall (d, writeData) List.mem_cons_self)]

/-- The same independence for a whole block. -/
theorem runBlock_state_indep (ind ind' : Nat → Byte) :
    ∀ (block : List (AccessDescriptor × ByteSeq)) (state : MemoryState),
      (runBlock state ind block).2 = (runBlock state ind' block).2
  | [], _ => rfl
  | (d, writeData) :: rest, state => by
    rw [runBlock, runBlock, applyAccess_state_indep state d writeData ind ind',
      runBlock_state_indep ind ind' rest _]

/-- The byte form, which is what a load's observation is read through. -/
theorem byteAt?_runBlock_of_untouched (indeterminate : Nat → Byte)
    (block : List (AccessDescriptor × ByteSeq)) (state : MemoryState) {id : AllocId}
    {offset : Nat} (hall : ∀ step ∈ block, ¬ Touches step id offset) :
    (runBlock state indeterminate block).2.byteAt? id offset = state.byteAt? id offset := by
  unfold MemoryState.byteAt?
  rw [cellAt?_runBlock_of_untouched indeterminate block state hall]

/--
**What a successful write stored survives the rest of an untouched block.**

The store is resolved once by `prepareAccess`; the covered readback theorem then
reads through that same allocation-to-backing mapping. Later steps need only avoid
the written allocation-local offset.
-/
theorem byteAt?_write_survives_block (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte)
    (block : List (AccessDescriptor × ByteSeq)) {record : AllocationRecord}
    (_hfound : state.allocations.lookup d.provenance.root = some record)
    (hden : denialOf state d = Option.none) (hwrites : d.intent.writes = true)
    {offset : Nat}
    (hcov : (ByteRange.mk d.range.start (writeData.take d.range.size).length).Covers offset)
    (hall : ∀ step ∈ block, ¬ Touches step d.provenance.root offset) :
    (runBlock (applyAccess state d writeData indeterminate).2 indeterminate
        block).2.byteAt? d.provenance.root offset =
      (writeData.take d.range.size)[offset - d.range.start]? := by
  rw [byteAt?_runBlock_of_untouched indeterminate block _ hall]
  obtain ⟨access, hprepared⟩ := (denialOf_eq_none_iff state d).mp hden
  rw [applyAccess_state, hprepared]
  simp only
  have hwritten : writtenBytes d writeData = some (writeData.take d.range.size) := by
    simp [writtenBytes, hwrites]
  rw [commitResolved_of_eq_some state d access _ _ _ hwritten]
  exact MemoryState.byteAt?_writeResolved_of_covers state access
    (writeData.take d.range.size) d.producesInitialized
    (writtenBytes_fits d writeData _ hwritten) hcov

end Grass.Memory
