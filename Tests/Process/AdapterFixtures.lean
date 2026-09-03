import Grass.Process.Sequential.Adapter

/-!
# The five canonical adapter fixtures

`docs/PROCESS.md` §4 names them, and this file is them:

> The canonical adapter fixture family includes a zero-effect transition,
> duplicate equal-valued effects with distinct occurrences, initially pending
> effects, issue-then-cancel, and result-plus-new-effect in one transition. Each
> fixture checks the exact `Pending` equation and child binding in both
> execution directions. Failure of those equations falls back to explicit
> process authoring; no adapter proof may weaken them to set membership or site
> possibility.

## What "both execution directions" is taken to mean

The forward direction is the easy one and it is what a careless fixture checks:
the machine's decision produces an elaborated step with these values. The
backward direction is the one with teeth: the elaboration admits *no other*
step from here on this event. A fixture that only exhibits a witness has shown
the relation is inhabited; a fixture that also pins it has shown the relation is
the intended one, which is the difference between "some step reaches this state"
and "this is the step".

Every fixture below does both, and the backward halves are named `_only`.

## Why the fifth fixture is the important one

`result_plus_new_effect` answers one `log` occurrence and issues another with
the *same demand value*. The demand-level pending bag is `{log "hi"}` before the
step and `{log "hi"}` after it — **unchanged** — while the occurrence bag has
had one element consumed and a different one issued.

So a `Pending` presented as a bag of demands, or checked by membership, would
see nothing happen across that step. That is precisely the weakening §4 forbids,
and `Grass/Process/Sequential/Adapter.lean` forbids it by deriving `Pending`
from the occurrence bag rather than accepting one. This fixture is what makes
that argument concrete rather than asserted.
-/

namespace Grass.Process.Tests.Adapter

open Grass.Process
open Grass.Specification

/-! ## A boundary and a machine that exercise all five -/

/-- Two effects: one that answers trivially, one that can be retried or cancelled. -/
inductive JobDemand
  | log (line : String)
  | fetch (key : Nat)
  deriving DecidableEq, Repr

/--
How a fetch can end.

`cancelled` is how cancellation reaches this authoring surface: the sequential
author has no cancel operation, so a cancelled effect is one whose *result* says
so. That is the honest shape here — `Grass/Process/Cancellation/Compose.lean`
holds the network-level machinery, and a machine that could withdraw its own
outstanding demand would be a second semantics, which law 17 forbids.
-/
inductive FetchOutcome
  | delivered (value : Nat)
  | retryLater
  | cancelled
  deriving DecidableEq, Repr

/-- The dependent answer schema. -/
def JobResult : JobDemand → Type
  | .log _ => Unit
  | .fetch _ => FetchOutcome

/-- The boundary. -/
@[reducible] def job : DriverBoundary.{0} where
  ExternalEvent := Unit
  Demand := JobDemand
  Result := JobResult
  Observation := String
  requirements := RequirementSet.empty

/-- Where the machine can be. -/
inductive JobState
  | boot
  | warming
  | logFirst
  | logSecond
  | polling
  | done
  deriving DecidableEq, Repr

/--
The decision function.

Read as a program: boot, warm up, log twice with the *same line*, then poll
until the fetch is delivered or cancelled. The two logs and the self-looping
poll are what make the duplicate-occurrence fixtures possible.
-/
def jobDecide : JobState → SequentialDecision job JobState Nat
  | .boot => .internal .warming ["boot"]
  | .warming => .internal .logFirst []
  | .logFirst => .effect (.log "hi") (fun _ => .logSecond)
  | .logSecond => .effect (.log "hi") (fun _ => .polling)
  | .polling => .effect (.fetch 7) (fun outcome =>
      match outcome with
      | .delivered _ => .done
      | .retryLater => .polling
      | .cancelled => .done)
  | .done => .terminal 0

/-- The rank: only the two internal decisions are constrained by it. -/
def jobRank : JobState → Nat
  | .boot => 2
  | .warming => 1
  | _ => 0

/--
The machine.

`Request := Bool` selects the start, which is the whole of what the
initially-pending fixture needs: an eager start is one whose first decision is
already an effect.
-/
def worker : SequentialMachine job where
  State := JobState
  Request := Bool
  Terminal := Nat
  initial := fun eager => if eager then .logFirst else .boot
  decide := jobDecide
  invariant := fun _ => True
  initialInvariant := fun _ => trivial
  internalPreserves := by intros; trivial
  effectResumes := by intros; trivial
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  rank := jobRank
  internalDecreases := by
    rintro state next observations decision
    cases state <;> cases decision <;> exact Nat.lt_succ_self _

/-! ## The occurrences, named -/

/-- The `log "hi"` issued at the first logging point. -/
def firstLog (age : Nat) : worker.Occurrence :=
  ⟨⟨age, .logFirst⟩, .log "hi", fun _ => .logSecond⟩

/-- The `log "hi"` issued at the second — the *same demand value*, a different site. -/
def secondLog (age : Nat) : worker.Occurrence :=
  ⟨⟨age, .logSecond⟩, .log "hi", fun _ => .polling⟩

/-- The `fetch 7` issued at the polling point, whichever pass this is. -/
def poll (age : Nat) : worker.Occurrence :=
  ⟨⟨age, .polling⟩, .fetch 7, fun outcome =>
    match outcome with
    | .delivered _ => .done
    | .retryLater => .polling
    | .cancelled => .done⟩

/-- Each is one the machine really issues, so none is invented. -/
theorem firstLog_issues (age : Nat) : (firstLog age).Issues := rfl
theorem secondLog_issues (age : Nat) : (secondLog age).Issues := rfl
theorem poll_issues (age : Nat) : (poll age).Issues := rfl

/-! ## Fixture 1 — a zero-effect transition -/

/-- Nothing is outstanding before the boot step. -/
theorem boot_holds_nothing : worker.held ⟨0, .boot⟩ = 0 := rfl

/-- Nor after it. -/
theorem warming_holds_nothing : worker.held ⟨1, .warming⟩ = 0 := rfl

/-- **Forward: the boot step is an elaborated step that issues nothing.** -/
theorem zero_effect_transition :
    (worker.elaborate).Step ⟨0, .boot⟩ .internal ⟨1, .warming⟩ 0 ["boot"] :=
  ⟨rfl, rfl, rfl⟩

/--
**Backward: it is the only one.**

Nothing else is reachable from `boot` on an internal event, so the fixture pins
the transition rather than exhibiting one.
-/
theorem zero_effect_transition_only {after : worker.Point}
    {issued : Bag worker.Occurrence} {observations : ObservationSegment String}
    (step : (worker.elaborate).Step ⟨0, .boot⟩ .internal after issued observations) :
    after = ⟨1, .warming⟩ ∧ issued = 0 ∧ observations = ["boot"] := by
  obtain ⟨age, issuedEq, decision⟩ := step
  obtain ⟨afterAge, afterState⟩ := after
  simp only at age
  subst age
  injection decision with stateEq observationsEq
  subst stateEq
  subst observationsEq
  exact ⟨rfl, issuedEq, rfl⟩

/-- **And the exact pending equation: nothing consumed, nothing issued.** -/
theorem zero_effect_pending :
    (worker.elaborate).Pending ⟨1, .warming⟩ =
      (worker.elaborate).Pending ⟨0, .boot⟩ + (0 : Bag worker.Occurrence).map worker.occurrenceDemand :=
  DirectRelationalProgram.pending_equation_of_internal zero_effect_transition

/-! ## Fixture 2 — duplicate equal-valued effects with distinct occurrences -/

/-- The two logging sites issue the same demand. -/
theorem the_two_logs_have_equal_demands (age other : Nat) :
    (firstLog age).demand = (secondLog other).demand := rfl

/-- **And are nonetheless distinct occurrences.** -/
theorem the_two_logs_are_distinct (age other : Nat) : firstLog age ≠ secondLog other := by
  intro same
  have sameState : JobState.logFirst = JobState.logSecond :=
    congrArg (fun occurrence => occurrence.point.state) same
  exact absurd sameState (by decide)

/--
**The sharper case: the same demand from the same state.**

The retry loop `polling → polling` issues `fetch 7` from `polling` on every
pass. State could not distinguish these and demand could not either; the
execution point does. This is the case that decides the whole occurrence-identity
design, so it is stated over an arbitrary pass rather than at two chosen ages.
-/
theorem two_passes_of_the_poll_are_distinct (age : Nat) :
    (poll age).demand = (poll (age + 1)).demand ∧ poll age ≠ poll (age + 1) := by
  refine ⟨rfl, ?_⟩
  intro same
  have sameAge : age = age + 1 := congrArg (fun occurrence => occurrence.point.age) same
  omega

/--
**Forward: a retried poll consumes one occurrence and issues a different one.**

The `retryLater` answer sends the machine back to `polling`, where it issues
`fetch 7` again — a new occurrence at a new point.
-/
theorem duplicate_occurrences_across_a_retry (age : Nat) :
    (worker.elaborate).Step ⟨age, .polling⟩ (.result (poll age) .retryLater)
      ⟨age + 1, .polling⟩ {poll (age + 1)} [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Backward: the retry lands exactly there and issues exactly that.** -/
theorem duplicate_occurrences_across_a_retry_only {age : Nat} {after : worker.Point}
    {issued : Bag worker.Occurrence} {observations : ObservationSegment String}
    (step : (worker.elaborate).Step ⟨age, .polling⟩ (.result (poll age) .retryLater)
      after issued observations) :
    after = ⟨age + 1, .polling⟩ ∧ issued = {poll (age + 1)} ∧ observations = [] := by
  obtain ⟨stepAge, issuedEq, _, resumed, noObservations⟩ := step
  obtain ⟨afterAge, afterState⟩ := after
  simp only at stepAge resumed
  subst stepAge
  subst resumed
  exact ⟨rfl, issuedEq, noObservations⟩

/--
**And the exact pending equation, at the occurrence level.**

One occurrence consumed, one issued, and `remainder` is the whole rest of the
bag — which here is empty, because a sequential machine holds at most one thing.
-/
theorem duplicate_occurrences_pending_equation (age : Nat) :
    Bag.ConsumeExactlyOneMatching (worker.held ⟨age, .polling⟩) (poll age) 0 ∧
      worker.held ⟨age + 1, .polling⟩ = 0 + {poll (age + 1)} := ⟨rfl, rfl⟩

/-! ## Fixture 3 — initially pending effects -/

/-- The eager start is already blocked on an effect. -/
theorem eager_start_holds_one :
    worker.held ⟨0, worker.initial true⟩ = {firstLog 0} := rfl

/-- **Forward: the start issues exactly that occurrence and no observations.** -/
theorem initially_pending :
    (worker.elaborate).Initial true ⟨0, .logFirst⟩ {firstLog 0} [] :=
  ⟨rfl, rfl, rfl⟩

/-- **Backward: no other start of that request issues anything else.** -/
theorem initially_pending_only {point : worker.Point} {issued : Bag worker.Occurrence}
    {observations : ObservationSegment String}
    (start : (worker.elaborate).Initial true point issued observations) :
    point = ⟨0, .logFirst⟩ ∧ issued = {firstLog 0} ∧ observations = [] := by
  obtain ⟨pointEq, issuedEq, observationsEq⟩ := start
  refine ⟨pointEq, ?_, observationsEq⟩
  subst pointEq
  exact issuedEq

/--
**And the pending bag at the start is not empty.**

The fixture would be worth nothing if it were: §4 asks for an *initially
pending* effect, and a start that held nothing would satisfy every equation
below vacuously.
-/
theorem initially_pending_is_nonempty :
    (worker.elaborate).Pending ⟨0, .logFirst⟩ = {JobDemand.log "hi"} := rfl

/-- The lazy start, by contrast, holds nothing — so the two are really different. -/
theorem lazy_start_holds_nothing :
    (worker.elaborate).Pending ⟨0, worker.initial false⟩ = 0 := rfl

/-! ## Fixture 4 — issue then cancel -/

/-- **Forward: a cancelled fetch is consumed and nothing replaces it.** -/
theorem issue_then_cancel (age : Nat) :
    (worker.elaborate).Step ⟨age, .polling⟩ (.result (poll age) .cancelled)
      ⟨age + 1, .done⟩ 0 [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Backward: that is the only place a cancellation can land.** -/
theorem issue_then_cancel_only {age : Nat} {after : worker.Point}
    {issued : Bag worker.Occurrence} {observations : ObservationSegment String}
    (step : (worker.elaborate).Step ⟨age, .polling⟩ (.result (poll age) .cancelled)
      after issued observations) :
    after = ⟨age + 1, .done⟩ ∧ issued = 0 ∧ observations = [] := by
  obtain ⟨stepAge, issuedEq, _, resumed, noObservations⟩ := step
  obtain ⟨afterAge, afterState⟩ := after
  simp only at stepAge resumed
  subst stepAge
  subst resumed
  exact ⟨rfl, issuedEq, noObservations⟩

/--
**The exact pending equation: the occurrence is gone, and nothing was invented
to replace it.**

`docs/FOUNDATION.md` law 5 at this layer — a cancelled effect does not quietly
stay outstanding, and does not quietly spawn a successor.
-/
theorem issue_then_cancel_pending_equation (age : Nat) :
    Bag.ConsumeExactlyOneMatching (worker.held ⟨age, .polling⟩) (poll age) 0 ∧
      worker.held ⟨age + 1, .done⟩ = 0 + (0 : Bag worker.Occurrence) := ⟨rfl, rfl⟩

/-- And the state it lands in is terminal, holding nothing to dispose of. -/
theorem cancelled_run_terminates (age : Nat) :
    (worker.elaborate).terminal true ⟨age + 1, .done⟩ (0 : Nat) := rfl

/-- So the terminal disposition is the empty partition, with nothing hidden in it. -/
theorem cancelled_run_disposes_of_nothing (age : Nat) :
    (worker.elaborate).Pending ⟨age + 1, .done⟩ = 0 := rfl

/-! ## Fixture 5 — a result and a new effect in one transition -/

/--
**Forward: the first log is answered and the second is issued, in one step.**

Consumed `{firstLog age}`, issued `{secondLog (age + 1)}` — two occurrences of
*equal demand value*.
-/
theorem result_plus_new_effect (age : Nat) :
    (worker.elaborate).Step ⟨age, .logFirst⟩ (.result (firstLog age) ())
      ⟨age + 1, .logSecond⟩ {secondLog (age + 1)} [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Backward: nothing else is admitted.** -/
theorem result_plus_new_effect_only {age : Nat} {after : worker.Point}
    {issued : Bag worker.Occurrence} {observations : ObservationSegment String}
    (step : (worker.elaborate).Step ⟨age, .logFirst⟩ (.result (firstLog age) ())
      after issued observations) :
    after = ⟨age + 1, .logSecond⟩ ∧ issued = {secondLog (age + 1)} ∧ observations = [] := by
  obtain ⟨stepAge, issuedEq, _, resumed, noObservations⟩ := step
  obtain ⟨afterAge, afterState⟩ := after
  simp only at stepAge resumed
  subst stepAge
  subst resumed
  exact ⟨rfl, issuedEq, noObservations⟩

/-- The occurrence equation, exact. -/
theorem result_plus_new_effect_pending_equation (age : Nat) :
    Bag.ConsumeExactlyOneMatching (worker.held ⟨age, .logFirst⟩) (firstLog age) 0 ∧
      worker.held ⟨age + 1, .logSecond⟩ = 0 + {secondLog (age + 1)} := ⟨rfl, rfl⟩

/--
**The demand bag does not move across this step.**

The whole argument for occurrence-indexed pending, in one line: before the step
the machine is waiting on `log "hi"`, and after it the machine is waiting on
`log "hi"`. A `Pending` presented as a bag of demand values sees nothing happen
here, and a membership check sees nothing happen either — while in fact one
occurrence was answered and a different one was issued.
-/
theorem demand_bag_is_blind_to_this_step (age : Nat) :
    (worker.elaborate).Pending ⟨age, .logFirst⟩ =
      (worker.elaborate).Pending ⟨age + 1, .logSecond⟩ := rfl

/-- **The occurrence bag is not.** -/
theorem the_occurrence_bag_is_not_blind (age : Nat) :
    worker.held ⟨age, .logFirst⟩ ≠ worker.held ⟨age + 1, .logSecond⟩ := by
  intro same
  have present : firstLog age ∈ worker.held ⟨age + 1, .logSecond⟩ := by
    rw [← same]
    exact Bag.mem_singleton.mpr rfl
  have atPoint := SequentialMachine.held_point present
  have sameState : JobState.logFirst = JobState.logSecond :=
    congrArg SequentialMachine.Point.state atPoint
  exact absurd sameState (by decide)

/-! ## Child binding -/

/--
**The step's landing state is exactly the answered occurrence's own
continuation.**

§4's `ExactSiteProtocolAndChildBinding` at a concrete step. The adapter did not
choose where the result goes; the occurrence carries it.
-/
theorem child_binding_is_exact (age : Nat) :
    (worker.elaborate).resumeOf (firstLog age) () ⟨age, .logFirst⟩ = ⟨age + 1, .logSecond⟩ := rfl

/-- And it agrees with the step, which is the field the program actually owes. -/
theorem child_binding_agrees_with_the_step (age : Nat) :
    (⟨age + 1, .logSecond⟩ : worker.Point) =
      (worker.elaborate).resumeOf (firstLog age) () ⟨age, .logFirst⟩ :=
  (worker.elaborate).stepBinding _ _ _ _ _ _ (result_plus_new_effect age)

/-- And the retry and cancel steps bind the same way, which §4 asks of each fixture. -/
theorem retry_binding_agrees_with_the_step (age : Nat) :
    (⟨age + 1, .polling⟩ : worker.Point) =
      (worker.elaborate).resumeOf (poll age) .retryLater ⟨age, .polling⟩ :=
  (worker.elaborate).stepBinding _ _ _ _ _ _ (duplicate_occurrences_across_a_retry age)

theorem cancel_binding_agrees_with_the_step (age : Nat) :
    (⟨age + 1, .done⟩ : worker.Point) =
      (worker.elaborate).resumeOf (poll age) .cancelled ⟨age, .polling⟩ :=
  (worker.elaborate).stepBinding _ _ _ _ _ _ (issue_then_cancel age)

/--
**Two bindings for one occurrence are the same binding.**

`issuing_occurrence_determined_by_point` at this machine: an occurrence that the
worker really issues is fixed by where it was issued, so there is no second
binding to disagree with the first.
-/
theorem no_second_binding (age : Nat) (other : worker.Occurrence)
    (issues : other.Issues) (samePoint : other.point = ⟨age, .logFirst⟩) :
    other = firstLog age :=
  SequentialMachine.issuing_occurrence_determined_by_point issues (firstLog_issues age) samePoint

/-! ## And what the adapter does not invent -/

/--
**An occurrence the machine does not issue is not held anywhere.**

The value exists — `Occurrence` is a plain structure — but nothing constructs
it, and `held_issues` is what says so. This is the "site possibility" half of
§4's prohibition: a demand that *could* be issued at a state is not an
occurrence that *is* outstanding there.
-/
theorem an_uninvited_occurrence_is_never_held (age : Nat) (point : worker.Point) :
    (⟨⟨age, .logFirst⟩, .fetch 99, fun _ => .done⟩ : worker.Occurrence) ∉
      worker.held point := by
  intro present
  have issues := SequentialMachine.held_issues present
  simp [SequentialMachine.Occurrence.Issues, worker, jobDecide] at issues

/-! ## Fixture 2, the other reading — two equal-valued effects outstanding at once -/

/-!
`docs/PROCESS.md` §4's gloss is "equal-valued demands retain multiplicity
through distinct occurrences", which reads most naturally as *two outstanding at
the same time*. The fixtures above cannot exhibit that, and not by oversight: a
`SequentialMachine` is blocked on one effect or on none, so
`SequentialMachine.elaborate_pending_card_le_one` proves the elaborated pending
bag never holds two things.

That is a limit of the authoring surface, not of the structure. The program
below is written directly against `DirectRelationalProgram` — what
`docs/PROOF_FEASIBILITY.md` §2 calls "the lower-level multi-effect relational
escape hatch" and §4 calls "the low-level `DirectRelationalProgram` escape
hatch" — and holds two occurrences of `log "hi"` at once. It is what makes
`DirectRelationalProgram.card_pending` an inhabited claim rather than a true
statement about an empty case.

**It answers them in either order**, which is what the fixture is really for and
what an earlier version could not do. That version's `resumeOf` computed the
successor from the occurrence alone, so the state reached by answering the
second occurrence could not depend on whether the first was still outstanding;
`stepBinding` then forced both orders into one state and the bag equation forced
a step to re-issue an occurrence it had already used. A local adversarial review
found it. `resumeOf` now takes the state it is answered at, and
`the_two_orders_reach_different_states` is the check.
-/

/-- Two occurrences, distinguished by nothing but their identity. -/
abbrev LogSlot : Type := Bool

/-- Which of the two are still outstanding. -/
abbrev LogState : Type := Bool × Bool

/--
A program holding both at once, answerable in either order.

`Bool × Bool` rather than a list of outstanding slots so that no state can hold
the *same* occurrence twice — which is what
`twoLogs_distinguishes_its_occurrences` needs, and what a list would have made
false at states no execution reaches.
-/
@[reducible] def twoLogs : DirectRelationalProgram job where
  State := LogState
  Request := Unit
  TerminalResult := Unit
  Occurrence := LogSlot
  demandOf := fun _ => .log "hi"
  resumeOf := fun slot _ outstanding =>
    if slot then (false, outstanding.2) else (outstanding.1, false)
  held := fun outstanding =>
    match outstanding with
    | (true, true) => Bag.ofList [true, false]
    | (true, false) => Bag.ofList [true]
    | (false, true) => Bag.ofList [false]
    | (false, false) => 0
  Initial := fun _ outstanding issued observations =>
    outstanding = (true, true) ∧ issued = Bag.ofList [true, false] ∧ observations = []
  Step := fun before event after issued observations =>
    match event with
    | .internal => False
    | .result slot _ =>
        (if slot then before.1 else before.2) = true ∧
          after = (if slot then (false, before.2) else (before.1, false)) ∧
          issued = 0 ∧ observations = []
  initialEquation := by
    rintro _ outstanding issued observations ⟨isStart, issuedEq, _⟩
    subst isStart
    exact issuedEq.symm
  transitionEquation := by
    rintro before event after issued observations step
    cases event with
    | internal => exact absurd step id
    | result slot answer =>
      obtain ⟨live, isNext, issuedEq, _⟩ := step
      subst isNext
      subst issuedEq
      obtain ⟨first, second⟩ := before
      cases slot <;> cases first <;> cases second <;>
        first
          | exact absurd live (by decide)
          | exact ⟨Bag.ofList [], rfl, by simp⟩
          | exact ⟨Bag.ofList [false], rfl, by simp⟩
          | exact ⟨Bag.ofList [true], Quotient.sound (List.Perm.swap false true []),
              by simp⟩
  stepBinding := by
    rintro before slot answer after issued observations ⟨_, isNext, _, _⟩
    exact isNext
  terminal := fun _ outstanding _ => outstanding = (false, false)
  terminalDisposition := by
    intro _ outstanding _ isTerminal
    subst isTerminal
    exact ⟨0, 0, 0, by simp⟩

/-- **Both outstanding occurrences carry the same demand value.** -/
theorem both_slots_demand_the_same : twoLogs.demandOf true = twoLogs.demandOf false := rfl

/-- **And they are distinct occurrences.** -/
theorem the_slots_are_distinct : (true : LogSlot) ≠ false := by decide

/--
**So the pending bag holds two things, both of them `log "hi"`.**

§4's "duplicate equal-valued effects with distinct occurrences", and the
instance that makes `DirectRelationalProgram.card_pending` say something. A
`Pending` that were a *set* of demands, or checked by membership, would report
one.
-/
theorem pending_holds_two_equal_demands :
    twoLogs.Pending (true, true) =
      Bag.ofList [JobDemand.log "hi", JobDemand.log "hi"] := rfl

/-- Counted, which is the form the multiplicity claim takes. -/
theorem pending_has_cardinality_two : (twoLogs.Pending (true, true)).card = 2 := rfl

/-! ### Both orders -/

/-- **Forward: the first may be answered first.** -/
theorem answering_the_first :
    twoLogs.Step (true, true) (.result true ()) (false, true) 0 [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **And the second may be answered first.** -/
theorem answering_the_second_first :
    twoLogs.Step (true, true) (.result false ()) (true, false) 0 [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Either way the remaining one can still be answered. -/
theorem finishing_after_the_first :
    twoLogs.Step (false, true) (.result false ()) (false, false) 0 [] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem finishing_after_the_second :
    twoLogs.Step (true, false) (.result true ()) (false, false) 0 [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Backward: no other step is admitted on that event from that state.** -/
theorem answering_the_first_only {after : twoLogs.State} {issued : Bag LogSlot}
    {observations : ObservationSegment String}
    (step : twoLogs.Step (true, true) (.result true ()) after issued observations) :
    after = (false, true) ∧ issued = 0 ∧ observations = [] := by
  obtain ⟨_, isNext, issuedEq, observationsEq⟩ := step
  exact ⟨isNext, issuedEq, observationsEq⟩

/--
**The two orders reach different states.**

The expressivity the earlier `resumeOf` could not deliver: answering `false`
from a state where `true` is still outstanding lands somewhere other than
answering it after `true` has gone.
-/
theorem the_two_orders_reach_different_states :
    ((false, true) : LogState) ≠ (true, false) := by decide

/--
**And the exact equation: one occurrence consumed, the other left outstanding.**

`remainder` is `{false}` rather than `0`, which is the case the sequential route
never reaches — there, a step always empties the bag.
-/
theorem answering_the_first_pending_equation :
    Bag.ConsumeExactlyOneMatching (twoLogs.held (true, true)) true (Bag.ofList [false]) ∧
      twoLogs.held (false, true) = Bag.ofList [false] + 0 := ⟨rfl, by simp⟩

/-! ### What the demand bag cannot see -/

/--
**The demand bag cannot tell which occurrence was answered.**

This is the whole argument for occurrence-indexed pending, exhibited rather than
asserted. After answering `true` and after answering `false` the program is in
genuinely different states — `the_two_orders_reach_different_states` — and the
demand bags are *equal*, because both hold one `log "hi"`.
-/
theorem the_demand_bag_cannot_tell_them_apart :
    twoLogs.Pending (false, true) = twoLogs.Pending (true, false) := rfl

/-- **The occurrence bag can.** -/
theorem the_occurrence_bag_can_tell_them_apart :
    twoLogs.held (false, true) ≠ twoLogs.held (true, false) := by
  intro same
  have present : (false : LogSlot) ∈ twoLogs.held (true, false) := by
    rw [← same]
    exact Bag.mem_ofList.mpr (by decide)
  exact absurd (Bag.mem_ofList.mp present) (by decide)

/-- Both have cardinality one, so counting cannot tell them apart either. -/
theorem counting_cannot_tell_them_apart :
    (twoLogs.Pending (false, true)).card = 1 ∧ (twoLogs.Pending (true, false)).card = 1 :=
  ⟨rfl, rfl⟩

/-! ### The obligations an explicitly authored program owes -/

/--
**This program distinguishes its outstanding occurrences.**

`DirectRelationalProgram.OccurrencesAreDistinct` discharged by hand, which is the
point of naming it: the sequential elaboration gets it from holding at most one
thing, and an explicitly authored program owes it. A program with
`Occurrence := Unit` holding two would fail exactly here, and so would this one
if its state were a *list* of outstanding slots — `[true, true]` is a value no
execution reaches and the obligation quantifies over every state.
-/
theorem twoLogs_distinguishes_its_occurrences : twoLogs.OccurrencesAreDistinct := by
  intro outstanding slot remainder consumes present
  obtain ⟨first, second⟩ := outstanding
  cases first <;> cases second <;> cases slot
  · exact absurd consumes Bag.not_consume_zero
  · exact absurd consumes Bag.not_consume_zero
  · have same : remainder = Bag.ofList [] :=
      Bag.ConsumeExactlyOneMatching.remainder_unique consumes rfl
    rw [same] at present
    exact absurd (Bag.mem_ofList.mp present) (by decide)
  · exact absurd (Bag.mem_ofList.mp consumes.mem) (by decide)
  · exact absurd (Bag.mem_ofList.mp consumes.mem) (by decide)
  · have same : remainder = Bag.ofList [] :=
      Bag.ConsumeExactlyOneMatching.remainder_unique consumes rfl
    rw [same] at present
    exact absurd (Bag.mem_ofList.mp present) (by decide)
  · have same : remainder = Bag.ofList [true] :=
      Bag.ConsumeExactlyOneMatching.remainder_unique consumes
        (Quotient.sound (List.Perm.swap false true []))
    rw [same] at present
    exact absurd (Bag.mem_ofList.mp present) (by decide)
  · have same : remainder = Bag.ofList [false] :=
      Bag.ConsumeExactlyOneMatching.remainder_unique consumes rfl
    rw [same] at present
    exact absurd (Bag.mem_ofList.mp present) (by decide)

/--
**And it re-issues nothing.**

`DirectRelationalProgram.IssuesFreshOccurrences`, discharged trivially because
no step of this program issues anything at all — which is itself worth stating,
since a program that only ever consumes is the easy case and the obligation is
there for the others.
-/
theorem twoLogs_issues_fresh_occurrences : twoLogs.IssuesFreshOccurrences := by
  rintro before event after issued observations step occurrence isIssued
  cases event with
  | internal => exact absurd step id
  | result slot answer =>
    obtain ⟨_, _, issuedEq, _⟩ := step
    rw [issuedEq] at isIssued
    exact absurd isIssued (by simp)

/--
**And every occurrence it holds can be answered, in whatever order.**

`DirectRelationalProgram.EveryHeldOccurrenceIsAnswerable` — the half of §4's
`binding` that `stepBinding` does not reach. Without it a program could hold an
occurrence forever, bind it to nothing, terminate, and declare it resolved.
-/
theorem twoLogs_answers_everything_it_holds : twoLogs.EveryHeldOccurrenceIsAnswerable := by
  intro outstanding slot present answer
  obtain ⟨first, second⟩ := outstanding
  refine ⟨_, 0, [], ?_, rfl, rfl, rfl⟩
  cases first <;> cases second <;> cases slot <;>
    first
      | rfl
      | exact absurd (Bag.mem_ofList.mp present) (by decide)
      | exact absurd present (by simp)

end Grass.Process.Tests.Adapter
