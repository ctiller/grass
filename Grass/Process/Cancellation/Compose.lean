import Grass.Process.Cancellation.Identity

/-!
# Sequencing cancellation regions

`docs/PROCESS.md` §3 works one example and puts the milestone's exit criterion in
it:

> ```text
> uncancellable |> cancelpoint |> uncancellable
> ```
>
> is a process with a cancellation policy. A request arriving in the first
> region is retained until the middle point. At that point cancellation can
> terminate with its exact custody disposition; if no request is pending, the
> second region runs and the process next terminates normally. A request
> arriving after that point is retained until the process's terminal boundary,
> where the ordinary terminal disposition must classify it. A bounded-
> cancellation claim therefore also needs the two uncancellable regions to
> terminate within named bounds or under named environment premises. **A
> forever-blocking uncancellable region cannot acquire eventual cancellation
> merely by being sequenced with a later point.**

That last sentence is the one worth proving, and it is the reason this module
exists rather than a `|>` that merely typechecks. It is easy to write a
composition operator under which sequencing a cancellable thing after an
uncancellable one produces something "cancellable", and such an operator is
worse than none: it would let an author claim eventual cancellation for a
process that can block forever before reaching its first point.

## What is modelled, and what is deferred

A straight-line composite is a list of regions, each with a mask and a
termination bound. That is enough to state every claim in the paragraph above,
and it is deliberately less than §3's `CancellationSummary`, whose fields
(`PendingCancellationCustody`, `CancellationDelayBoundOrEnvironmentPending`,
`CancellationDispositionAt`, `ProcessTerminationContract`) are types the corpus
names and does not declare. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §5 schedules
those with the termination contract; inventing them here to make the summary
look complete would be the opposite of useful.

What this module does own is the *algebra*: composition, its associativity, and
the four facts the worked example asserts.

## A request is never silently dropped

§3: a cancellation request "is an affine occurrence: while execution is in an
uncancellable region it may be latched as `PendingCancellation`, but it may not
be silently dropped or acted upon at an arbitrary instruction."

`resolvedFrom` is that as a function: given the region a request arrives in, it
returns the first region at or after it that may act on the request, or `none`
if the request is retained to the terminal boundary. There is no third answer,
which is `request_is_latched_or_acted_on` — the law 7 statement for cancellation
requests, and the reason `resolvedFrom` is total rather than partial.
-/

namespace Grass.Process

/--
Whether a mask may act on a pending cancellation request.

`docs/PROCESS.md` §3's three-way mask, read as a question about requests.
`uncancellable` latches, and the other two may act — `cancellationPoint`
"observes the exact request/result race", and `interruptible` "admits delivery
between any two steps".
-/
def CancellationMask.MayAct : CancellationMask → Bool
  | .uncancellable => false
  | .cancellationPoint => true
  | .interruptible => true

@[simp] theorem CancellationMask.mayAct_uncancellable :
    CancellationMask.uncancellable.MayAct = false := rfl

@[simp] theorem CancellationMask.mayAct_point :
    CancellationMask.cancellationPoint.MayAct = true := rfl

/--
One straight-line region of a process.

`bound` is `docs/PROCESS.md` §3's "terminate within named bounds": a number of
steps after which the region must end, or `none` for a region that may block
forever. The `none` case is not an oversight to be tidied away — it is the whole
subject of `unbounded_region_defeats_cancellation` below.
-/
structure CancellationRegion where
  /-- What this region does with a pending request. -/
  mask : CancellationMask
  /-- The named bound on its duration, or `none` if it may block forever. -/
  bound : Option Nat
  deriving DecidableEq, Repr

namespace CancellationRegion

/-- A region that promises to end. -/
def Bounded (region : CancellationRegion) : Prop := region.bound ≠ none

/-- An uncancellable region that may block forever: the dangerous one. -/
def BlocksForever (region : CancellationRegion) : Prop :=
  region.mask = .uncancellable ∧ region.bound = none

theorem blocksForever_not_bounded {region : CancellationRegion}
    (blocks : region.BlocksForever) : ¬ region.Bounded :=
  fun bounded => bounded blocks.2

end CancellationRegion

/--
A straight-line composite: regions in order.

`docs/PROCESS.md` §3's `|>`. A list rather than a binary tree, because the
operator's associativity is the thing to prove and a list makes it
`List.append_assoc` rather than an induction — the composite that matters is the
sequence, not the bracketing.
-/
structure CancellationSequence where
  /-- The regions, in execution order. -/
  regions : List CancellationRegion
  deriving DecidableEq, Repr

namespace CancellationSequence

/-- `docs/PROCESS.md` §3's `|>`. -/
def seq (before after : CancellationSequence) : CancellationSequence :=
  ⟨before.regions ++ after.regions⟩

/-- One region on its own. -/
def one (region : CancellationRegion) : CancellationSequence := ⟨[region]⟩

/-- The empty composite, which is `seq`'s identity. -/
def nothing : CancellationSequence := ⟨[]⟩

@[simp] theorem seq_regions (before after : CancellationSequence) :
    (before.seq after).regions = before.regions ++ after.regions := rfl

/--
**Composition is associative.**

Half of `docs/PROCESS_IMPLEMENTATION_PLAN.md` §5's exit criterion, and the
reason a composite is a list: bracketing `a |> (b |> c)` differently from
`(a |> b) |> c` cannot change what the process does, so the algebra must not be
able to tell them apart.
-/
theorem seq_assoc (a b c : CancellationSequence) :
    (a.seq b).seq c = a.seq (b.seq c) := by
  simp [seq, List.append_assoc]

@[simp] theorem seq_nothing (a : CancellationSequence) : a.seq nothing = a := by
  cases a; simp [seq, nothing]

@[simp] theorem nothing_seq (a : CancellationSequence) : nothing.seq a = a := by
  cases a; simp [seq, nothing]

/-! ## Where a request goes -/

/--
The first region at or after `arrival` that may act on a pending request, or
`none` if the request is retained to the terminal boundary.

Total, which is the point: `docs/PROCESS.md` §3 says a request "may not be
silently dropped", so every request has an answer here — a region that acts on
it, or the terminal boundary. There is no third case and no partiality to hide
one in.
-/
def resolvedFrom (sequence : CancellationSequence) (arrival : Nat) : Option Nat :=
  let rec search : List CancellationRegion → Nat → Option Nat
    | [], _ => none
    | region :: rest, index =>
        if region.mask.MayAct then some index else search rest (index + 1)
  search (sequence.regions.drop arrival) arrival

/--
**A request is latched or acted on, and never both or neither.**

`docs/FOUNDATION.md` law 7 for cancellation requests. The disjunction is
exhaustive because `resolvedFrom` is a total function into `Option`, and
exclusive because an `Option` is `some` or `none`.

Trivial as a proof and not as a design: it is the statement that a request's
fate is determined by where it arrived, rather than by a scheduler's choice at
an arbitrary instruction.
-/
theorem request_is_latched_or_acted_on (sequence : CancellationSequence)
    (arrival : Nat) :
    (∃ index, sequence.resolvedFrom arrival = some index) ∨
      sequence.resolvedFrom arrival = none := by
  cases resolution : sequence.resolvedFrom arrival with
  | none => exact Or.inr rfl
  | some index => exact Or.inl ⟨index, rfl⟩

/-! ## Bounded cancellation -/

/--
Every region promises to end.

`docs/PROCESS.md` §3: "A bounded-cancellation claim therefore also needs the two
uncancellable regions to terminate within named bounds or under named
environment premises."
-/
def Bounded (sequence : CancellationSequence) : Prop :=
  ∀ region ∈ sequence.regions, region.Bounded

/-- Some region may act on a request. -/
def HasCancellationPoint (sequence : CancellationSequence) : Prop :=
  ∃ region ∈ sequence.regions, region.mask.MayAct

/--
**Eventual cancellation: a request is acted on, and the wait is bounded.**

Both halves, because either alone is worthless. A composite with a point but an
unbounded region ahead of it may never reach the point; a composite that is
bounded throughout but has no point never acts on a request at all.
-/
def EventuallyCancellable (sequence : CancellationSequence) : Prop :=
  sequence.HasCancellationPoint ∧ sequence.Bounded

/--
**A forever-blocking region defeats the claim, wherever it sits.**

`docs/PROCESS.md` §3's closing sentence: "A forever-blocking uncancellable
region cannot acquire eventual cancellation merely by being sequenced with a
later point."

Stated over an arbitrary sequence and an arbitrary position, so it covers the
case the sentence warns about — an unbounded region *before* the point — and
equally the case an author is likelier to write by accident, an unbounded
region after it.
-/
theorem unbounded_region_defeats_cancellation {sequence : CancellationSequence}
    {region : CancellationRegion} (present : region ∈ sequence.regions)
    (blocks : region.BlocksForever) : ¬ sequence.EventuallyCancellable :=
  fun cancellable =>
    region.blocksForever_not_bounded blocks (cancellable.2 region present)

/--
And sequencing does not repair it: if either side blocks forever, so does the
composite.

The operator-level statement of the same fact, which is what stops `|>` from
being the kind of composition that manufactures a guarantee.
-/
theorem seq_inherits_unboundedness {before after : CancellationSequence}
    {region : CancellationRegion}
    (present : region ∈ before.regions ∨ region ∈ after.regions)
    (blocks : region.BlocksForever) : ¬ (before.seq after).EventuallyCancellable := by
  refine unbounded_region_defeats_cancellation ?_ blocks
  rw [seq_regions]
  exact present.elim (List.mem_append_left _) (List.mem_append_right _)

/-- Conversely, a bounded composite is bounded on both sides. -/
theorem seq_bounded_iff {before after : CancellationSequence} :
    (before.seq after).Bounded ↔ before.Bounded ∧ after.Bounded := by
  constructor
  · intro bounded
    exact ⟨fun region present => bounded region (by simp [present]),
      fun region present => bounded region (by simp [present])⟩
  · rintro ⟨beforeBounded, afterBounded⟩ region present
    rw [seq_regions] at present
    exact (List.mem_append.mp present).elim (beforeBounded region) (afterBounded region)

end CancellationSequence

end Grass.Process
