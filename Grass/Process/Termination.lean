import Grass.Process.Cancellation.Compose
import Grass.Process.Run

/-!
# Typed termination

`docs/PROCESS.md` §3 states the principle before it states the type:

> The valuable principle is typed termination, not "let it crash".

and then the sentence that does the work:

> Forced termination is legal only at a proved safe point, or else uses a
> separately modeled fault containment/escalation path; it never retroactively
> validates arbitrary partially executed instructions.

`noArbitraryDeath` below is that sentence, and it is the only field of the
contract that cannot be weakened without the whole thing becoming decoration.
Everything else here exists to make it say something: a `SafePoint` predicate
for it to range over, a `Cause` for a termination to be *for*, and a disposition
that accounts for what the process was holding when it stopped.

## What a disposition is, at this layer

`docs/PROCESS.md` §3 asks a disposition to transfer "all state, resources, loans
and obligations". Resources and loans are `c-mem`'s and obligations are too, so
this layer states the part it owns: the outstanding *demands*, exactly
partitioned into resolved, transferred and pending by
`Grass/Process/Run.lean`'s `TerminalDemandClassification`.

That reuse is the point rather than a convenience. The classification already
carries `card_partition` — multiplicity is conserved, so the three parts account
for every occurrence *counted* — which is what stops a disposition claiming to
have disposed of a bag while its parts hold fewer occurrences than the bag did.
A fresh disposition type here would have had to re-earn that, and an earlier
revision of the run layer got exactly this wrong by using a multiplicity-blind
membership predicate.

## Two ways this record was uninhabitable, and how the fixture found them

Both are worth recording because they are the same defect twice, and it is the
one this repository has already been bitten by: a field quantified over more
situations than can actually arise.

The first draft required a `TerminalDisposition` for *every* permitted
termination, including a faulted one. A `TerminalDisposition` contains
`p.Terminal request state result`, and a faulting process stops in whatever
state it faulted from — `Grass/Process/Network/Instance.lean` says so directly.
So any process that could fault away from a terminal state had no contract at
all. `disposition` now carries a `mode ≠ .faulted` guard, which is also the
faithful reading of §3's "separately modeled fault containment path", and
`FaultCustodyObligation` names what that path still owes.

The second draft let `permitted` see the mode, cause and state but not the
outstanding demands, while `disposition` quantified over every bag. A
specification whose `TerminalRemainderLaw` is `strict` accepts only an empty
remainder, so no disposition exists for a non-empty bag and the record was again
uninhabitable — at a law the corpus supplies by name. `permitted` now indexes on
the bag, which is the honest statement anyway: whether a process may stop
depends on what it is holding.

Neither was found by reading the module. Both were found by trying to write
`Tests/Process/TerminationFixtures.lean` against a countdown whose remainder law
permits up to two pending ticks, which is exactly what a fixture is for.

## The liveness half is not here, and is not pretended to be

§3's contract also carries

```text
reachesSafePoint : forall cause run,
  requested cause run.current -> TerminationPremises p cause run ->
  Eventually run (fun state => SafePoint state ∧ permitted .cooperative cause state)
```

and that is the *cooperative cancellation liveness theorem*, which
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §5 says is what makes cooperative
cancellation a liveness theorem plus an exact custody theorem rather than one of
them.

It is not stated here because it cannot be stated honestly yet. `Eventually`
over a run quantifies over fair continuations, and this layer has `Reachable`
but no fairness model and no `TerminationPremiseFamily`; a predicate written as
"some reachable state satisfies it" would be *possibly*, not *eventually*, and
would read as the liveness theorem while proving nothing about scheduling.
`ReachesSafePointObligation` below names the obligation and its owner instead,
so it is deferred rather than lost.

`Grass/Process/Cancellation/Compose.lean`'s bounded-cancellation algebra is the
part of that argument this milestone *can* discharge, and it does: a composite
with an unbounded region is not eventually cancellable however many points
follow it.
-/

namespace Grass.Process

universe u w

/--
How a process may stop.

`docs/PROCESS.md` §3's three modes. The asymmetry between them is the whole
subject: two of the three require a proved safe point and the third does not,
which is what `noArbitraryDeath` says and what makes `faulted` the mode a
contract cannot use to escape its own obligations.
-/
inductive TerminationMode
  /-- The process reached a point and stopped because it was asked to. -/
  | cooperative
  /-- Something stopped it, at a point where stopping was proved safe. -/
  | forcedAtSafePoint
  /-- It failed. The only mode that may occur away from a safe point. -/
  | faulted
  deriving DecidableEq, Repr

/--
What a terminating process does with what it was holding.

`docs/PROCESS.md` §3's `TerminalDisposition`, at the granularity this layer
owns. The result and its terminality say the process genuinely finished; the
classification says what became of every outstanding demand.
-/
structure TerminalDisposition {p : ProcessSpec.{u, w}} (law : TerminalRemainderLaw p)
    (request : p.Request) (state : p.State) (outstanding : Bag p.Demand) where
  /-- The answer the process finished with. -/
  result : p.TerminalResult
  /-- And it really is a terminal state for it. -/
  terminal : p.Terminal request state result
  /-- Exactly what became of every outstanding occurrence. -/
  classification : TerminalDemandClassification law request state result outstanding

namespace TerminalDisposition

variable {p : ProcessSpec.{u, w}} {law : TerminalRemainderLaw p}
  {request : p.Request} {state : p.State} {outstanding : Bag p.Demand}

/--
**Nothing is dropped when a process stops.**

Straight from `TerminalDemandClassification.card_partition`: the three parts
account for every outstanding occurrence, counted. A disposition that resolved
one of two identical pending demands and called the bag disposed of would fail
this, which is the defect the classification was rebuilt to prevent.
-/
theorem accounts_for_everything
    (disposition : TerminalDisposition law request state outstanding) :
    outstanding.card =
      disposition.classification.resolved.card +
        disposition.classification.transferred.card +
        disposition.classification.pending.card :=
  disposition.classification.card_partition

/-- And the specification permitted this particular split. -/
theorem is_permitted (disposition : TerminalDisposition law request state outstanding) :
    law.Accepts request state disposition.result
      disposition.classification.resolved
      disposition.classification.transferred
      disposition.classification.pending :=
  disposition.classification.permitted

end TerminalDisposition

/--
**The contract a process exports about how it may stop.**

`docs/PROCESS.md` §3's `ProcessTerminationContract`, with the liveness and
escalation fields deferred; see the module note for why, and
`ReachesSafePointObligation` for where they went.
-/
structure ProcessTerminationContract {p : ProcessSpec.{u, w}}
    (law : TerminalRemainderLaw p) (request : p.Request) where
  /-- The states at which stopping is safe. -/
  SafePoint : p.State → Prop
  /-- Why a termination might be asked for. -/
  Cause : Type
  /-- A termination of this cause has been requested at this state. -/
  requested : Cause → p.State → Prop
  /--
  This mode of termination, for this cause, is allowed at this state while
  holding these demands.

  The outstanding bag is an index rather than an afterthought. Whether a process
  may stop depends on what it is holding: a specification whose
  `TerminalRemainderLaw` is `strict` permits stopping only with nothing
  outstanding, and a `permitted` that could not see the bag would have to claim
  otherwise. See the module note on uninhabitability.
  -/
  permitted : TerminationMode → Cause → p.State → Bag p.Demand → Prop
  /--
  **No arbitrary death.**

  `docs/PROCESS.md` §3: forced termination "is legal only at a proved safe
  point, or else uses a separately modeled fault containment/escalation path; it
  never retroactively validates arbitrary partially executed instructions."

  The disjunction is the containment path: a fault may happen anywhere, and
  everything else may not. Without this field the contract would permit stopping
  a process midway through an operation and calling the result a termination,
  which is what "let it crash" gets wrong and what typed termination is for.
  -/
  noArbitraryDeath : ∀ mode cause state outstanding,
    permitted mode cause state outstanding → SafePoint state ∨ mode = .faulted
  /--
  Every permitted termination *that reaches a safe point* has an exact
  disposition.

  Total over those, so there is no permitted orderly stop that leaves the
  outstanding demands unaccounted for — and deliberately not total over the
  faulted ones, which is the second half of §3's sentence: a fault uses "a
  separately modeled fault containment/escalation path", and a faulting process
  stops in whatever state it faulted from rather than in a terminal one.
  `FaultCustodyObligation` names what owns that path.
  -/
  disposition : ∀ mode cause state outstanding,
    permitted mode cause state outstanding → mode ≠ .faulted →
    TerminalDisposition law request state outstanding

namespace ProcessTerminationContract

variable {p : ProcessSpec.{u, w}} {law : TerminalRemainderLaw p} {request : p.Request}
  (contract : ProcessTerminationContract law request)

/--
**A forced termination happens at a safe point.**

The first half of §3's sentence, with the fault escape ruled out by the mode
itself: `forcedAtSafePoint` is not `faulted`, so `noArbitraryDeath`'s disjunction
collapses to the safe point.
-/
theorem forced_termination_is_safe {cause : contract.Cause} {state : p.State}
    {outstanding : Bag p.Demand}
    (allowed : contract.permitted .forcedAtSafePoint cause state outstanding) :
    contract.SafePoint state := by
  rcases contract.noArbitraryDeath _ cause state outstanding allowed with safe | faulted
  · exact safe
  · exact absurd faulted (by decide)

/-- And so does a cooperative one. -/
theorem cooperative_termination_is_safe {cause : contract.Cause} {state : p.State}
    {outstanding : Bag p.Demand}
    (allowed : contract.permitted .cooperative cause state outstanding) :
    contract.SafePoint state := by
  rcases contract.noArbitraryDeath _ cause state outstanding allowed with safe | faulted
  · exact safe
  · exact absurd faulted (by decide)

/--
**A process cannot be stopped away from a safe point except by failing.**

The contrapositive, and the form a caller wants: at a state that is not a safe
point, the only permitted mode is `faulted`. This is what stops a supervisor
manufacturing a forced stop wherever it likes — §3 says a supervisor "cannot
manufacture a safe forced stop", and this is that.
-/
theorem only_a_fault_happens_off_a_safe_point {mode : TerminationMode}
    {cause : contract.Cause} {state : p.State} {outstanding : Bag p.Demand}
    (unsafe' : ¬ contract.SafePoint state)
    (allowed : contract.permitted mode cause state outstanding) : mode = .faulted := by
  rcases contract.noArbitraryDeath mode cause state outstanding allowed with safe | faulted
  · exact absurd safe unsafe'
  · exact faulted

/--
And every permitted stop, in any mode, accounts for what was outstanding.

The safety half assembled: a termination is permitted only where
`noArbitraryDeath` allows, and wherever it is permitted the demands are exactly
partitioned. There is no permitted stop that loses an occurrence.
-/
theorem orderly_stops_account_for_everything {mode : TerminationMode}
    {cause : contract.Cause} {state : p.State} {outstanding : Bag p.Demand}
    (allowed : contract.permitted mode cause state outstanding)
    (orderly : mode ≠ .faulted) :
    outstanding.card =
      (contract.disposition mode cause state outstanding allowed
        orderly).classification.resolved.card +
        (contract.disposition mode cause state outstanding allowed
          orderly).classification.transferred.card +
        (contract.disposition mode cause state outstanding allowed
          orderly).classification.pending.card :=
  (contract.disposition mode cause state outstanding allowed
    orderly).accounts_for_everything

/--
**The fault path's obligation, named rather than discharged.**

`docs/PROCESS.md` §3 sends a fault down "a separately modeled fault
containment/escalation path". `disposition` therefore does not cover it, and
this is what covers it instead: whatever owns that path must still account for
the demands a faulting process was holding.

Named here rather than left implicit, because the alternative reading of
`disposition`'s `mode ≠ .faulted` guard is that a faulting process's outstanding
demands simply do not matter, and that is `docs/FOUNDATION.md` law 7. They
matter; they are somebody else's to account for.
-/
def FaultCustodyObligation
    (custody : contract.Cause → p.State → Bag p.Demand → Prop) : Prop :=
  ∀ cause state outstanding,
    contract.permitted .faulted cause state outstanding →
    custody cause state outstanding

/--
**The liveness obligation, named rather than proved.**

`docs/PROCESS.md` §3's `reachesSafePoint`: under the contract's own premises, a
requested cooperative termination *reaches* a safe point at which it is
permitted. Cooperative cancellation is that theorem together with the exact
custody theorem above, and this layer can state the second and not the first.

Written as a predicate over a supplied `Eventually` rather than as a field,
because a field would have to be discharged and nothing here can discharge it
honestly: `Eventually` quantifies over fair continuations, and this layer has
`Grass/Process/Run.lean`'s `Reachable` but no fairness model and no
`TerminationPremiseFamily`. A "some reachable state satisfies it" stand-in would
be *possibly* rather than *eventually*, and would read as the liveness theorem
while proving nothing about scheduling.

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §5 owns it. What is dischargeable today is
`Grass/Process/Cancellation/Compose.lean`'s bounded-cancellation algebra, which
is the part of the argument that does not need fairness.

**The quantifier placement matters and an earlier version had it wrong.**
`outstanding` was bound *outside* `Eventually`, so the obligation demanded a
later state permitted while holding *every* bag — unsatisfiable for this
module's own fixture contract, which local adversarial review demonstrated in
one line. It is now bound inside and existentially: the process reaches a safe
point at which a cooperative stop is *possible*.

That is weaker than the claim a reader wants, which is about the bag the process
is actually holding when it gets there — and that bag lives in
`Grass/Process/Run.lean`'s run state, not in `p.State`. The same layering that
makes this an obligation rather than a field is what stops it being stated
exactly.

The obligation remains free in two other directions and this is not a defect to
route around: `Eventually` and `Premises` are both author-supplied, so
`Eventually := fun _ _ => True` or `Premises := fun _ _ => False` discharges it.
Nothing here can constrain `Eventually` to be a liveness modality, because this
layer has no fairness model — which is the reason it is a named obligation
rather than a field. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.52 records it.
-/
def ReachesSafePointObligation
    (Premises : contract.Cause → p.State → Prop)
    (Eventually : p.State → (p.State → Prop) → Prop) : Prop :=
  ∀ cause state, contract.requested cause state →
    Premises cause state →
    Eventually state fun later =>
      contract.SafePoint later ∧
        ∃ outstanding, contract.permitted .cooperative cause later outstanding

end ProcessTerminationContract

end Grass.Process
