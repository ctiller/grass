import Grass.Process.Function.Serial
import Tests.Process.M1Fixtures

/-!
# A serial call that collapses, and one that must not

`Grass/Process/Function/Serial.lean` claims that a computation whose answer
comes from outside cannot be a serial call. Both halves are here.

* `doubling` is a pure routine over a two-field state. It has a contract, a
  machine that realizes it, a proved work bound, and a collapse into one process
  transition. `the_answer_is_determined` reads the determinacy back off the
  collapse.
* `blockingRead` is the counterexample local adversarial review built against an
  earlier version of the module: its post-state depends on how many bytes
  arrived, and every other field is satisfiable — including a *non-degenerate*
  footprint. `a_blocking_read_has_no_realizing_source` is the refusal, and it
  holds for **every** source, not merely for the obvious ones.

The second is the fixture that matters. Before `SerialFunctionRealizes.converse`
existed, `blockingRead` had a source and a collapse, and the module's
frontier-freedom argument was a fact about a type nothing required.
-/

namespace Grass.Process.Tests.Serial

open Grass.Process
open Grass.Process.Tests

/-! ## A pure routine -/

/-- A counter and a field the routine must not touch. -/
abbrev Cell : Type := Nat × Nat

/--
Doubling the counter.

The footprint is genuine: it says the second field does not move, and
`footprintSeparates` is discharged by two states that differ there. A
`fun _ _ => True` footprint would satisfy `postWithinFootprint` and fail this.
-/
def doubling : SerialFunctionContract Cell where
  Input := Unit
  Output := Unit
  Fault := Empty
  ExitState := Unit
  Obligations := Unit
  Resources := Unit
  Pre := fun _ _ => True
  disposition := fun _ => .returned ()
  Post := fun _ _ before after => after = (before.1 * 2, before.2)
  obligations := fun _ _ before after => after = before
  resources := fun _ _ before after => after = before
  footprintAgrees := fun before after => before.2 = after.2
  postWithinFootprint := by
    rintro _ _ before after rfl
    rfl
  footprintSeparates := ⟨(0, 0), (0, 1), by decide⟩
  faultCustody := fun fault _ _ _ _ _ _ => fault.elim
  faultsDeclared := by
    rintro _ _ fault _ _ _ _ _ _ _ _ _ _
    exact fault.elim
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  workBound := some (fun _ _ => 1)

/-- Where the machine ends up, for any starting cell. -/
def doubled (cell : Cell) : Cell × Bool := ((cell.1 * 2, cell.2), true)

/-- What the machine does: one internal step doubles, then it exits. -/
def doublingDecide (state : Cell × Bool) : SerialDecision (Cell × Bool) Unit :=
  if state.2 then .exit () else .internal (doubled state.1)

/-- Its measure: one before the doubling, zero after. -/
def doublingRank (state : Cell × Bool) : Nat := if state.2 then 0 else 1

/-- The machine. -/
def doublingSource : SerialFunctionSource doubling where
  Machine := Cell × Bool
  enter := fun _ before => (before, false)
  read := fun state => state.1
  enterReads := fun _ _ => rfl
  decide := doublingDecide
  rank := doublingRank
  internalDecreases := by
    rintro ⟨cell, done⟩ next decision
    cases done with
    | true => exact absurd decision (by simp [doublingDecide])
    | false =>
      simp only [doublingDecide, Bool.false_eq_true, if_false] at decision
      injection decision with isDoubled
      subst isDoubled
      exact Nat.zero_lt_one

theorem doubling_decides_at_entry (cell : Cell) :
    doublingSource.decide (cell, false) = .internal (doubled cell) := rfl

theorem doubling_decides_at_exit (cell : Cell) :
    doublingSource.decide (doubled cell) = .exit () := rfl

/-- The machine's whole execution from any entry, as a single witness. -/
theorem doubling_runs (cell : Cell) :
    doublingSource.InternalSteps (cell, false) (doubled cell) :=
  .step (doubling_decides_at_entry cell) (.refl _)

/-- **And that is the only place it can stop**, by `exit_is_unique`. -/
theorem doubling_stops_only_there (cell : Cell) {finish : doublingSource.Machine}
    (steps : doublingSource.InternalSteps (cell, false) finish)
    (atExit : (doublingSource.decide finish).IsExit) : finish = doubled cell :=
  SerialFunctionSource.exit_is_unique steps atExit (doubling_runs cell)
    (by rw [doubling_decides_at_exit cell]; trivial)

/--
**The machine realizes the contract.**

`converse` is the field that costs something: every state the contract permits
has to be one the machine reaches, and here that pins `after` to
`(before.1 * 2, before.2)`.
-/
theorem doubling_is_realized : SerialFunctionRealizes doubling doublingSource where
  exitsPost := by
    rintro _ before finish _ _ steps atExit
    have same : finish = doubled before :=
      doubling_stops_only_there before steps (by rw [atExit]; trivial)
    rw [same]
    rfl
  bounded := by
    rintro bound isSome input before _
    injection isSome with same
    subst same
    exact ⟨doubled before,
      .step (doubling_decides_at_entry before) (.refl 0 _),
      by rw [doubling_decides_at_exit before]; trivial⟩

/-- **The implementation `doubling` actually selects.** -/
def doublingBehavior : ExactSerialBehavior doubling where
  exitOf := fun _ _ => ()
  after := fun _ cell => (cell.1 * 2, cell.2)

/-- **And it refines the contract**, which is all a caller needs. -/
theorem doublingBehavior_refines : doublingBehavior.Refines := by
  intro _ _ _
  rfl

/-- **And the machine runs exactly what `doublingBehavior` selects.** -/
theorem doubling_is_realized_exactly :
    SerialFunctionRealizesExactly doublingBehavior doublingSource where
  onlyThatExit := by
    rintro _ before finish _ _ steps atExit
    have same : finish = doubled before :=
      doubling_stops_only_there before steps (by rw [atExit]; trivial)
    subst same
    exact ⟨rfl, rfl⟩
  converse := by
    rintro _ before _
    exact ⟨doubled before, doubling_runs before, doubling_decides_at_exit before, rfl⟩

/-- **So a caller who has the machine knows which answer it runs**, without the
contract having had to promise there is only one. -/
theorem doubling_runs_the_selection (before : Cell) {finish : doublingSource.Machine}
    {exitState : doubling.ExitState}
    (steps : doublingSource.InternalSteps (doublingSource.enter () before) finish)
    (atExit : doublingSource.decide finish = .exit exitState) :
    doublingSource.read finish = doublingBehavior.after () before :=
  (doubling_is_realized_exactly.onlyThatExit () before finish exitState trivial
    steps atExit).2

/-- And its claimed work bound is one the machine meets. -/
theorem doubling_is_responsive : doubling.Responsive := ⟨_, rfl⟩

/-! ## The collapse -/

/-- A process whose whole step relation is one doubling call. -/
def doublingProcess : ProcessSpec.{0, 0} where
  vocabulary := countdownVocabulary
  Request := Unit
  State := Cell
  TerminalResult := Unit
  Initial := fun _ state issued emitted => state = (0, 0) ∧ issued = 0 ∧ emitted = []
  Terminal := fun _ _ _ => False
  Step := fun before _ after issued emitted =>
    after = (before.1 * 2, before.2) ∧ issued = 0 ∧ emitted = []
  view := none

/--
**And the call collapses into one of its transitions.**

`source` and `realizes` are fields of `CollapsesToOneTransition`, so producing
this required producing the frontier-freedom argument — which is the whole
change local adversarial review forced. `Exclusive` is `True` here because this
process's state is the routine's alone; a plan where it were shared would owe a
linearization point instead.
-/
def doublingCollapses :
    CollapsesToOneTransition (p := doublingProcess) doubling (fun _ _ => True)
      Unit (fun _ _ _ => True) (fun _ _ _ => True) (.external .wake) where
  source := doublingSource
  realizes := doubling_is_realized
  behavior := doublingBehavior
  exact := doubling_is_realized_exactly
  refines := doublingBehavior_refines
  sound := by
    rintro _ _ before after _ rfl
    exact ⟨rfl, rfl, rfl⟩
  demandFree := by
    rintro _ _ before after issued emitted _ _ ⟨_, noDemands, noObservations⟩
    exact ⟨noDemands, noObservations⟩
  visibility := fun _ _ _ => .exclusive trivial

/-- **The transition issues nothing — bounded, not merely witnessed.** -/
theorem the_collapse_issues_nothing (before after : Cell)
    (issued : Bag doublingProcess.Demand)
    (emitted : ObservationSegment doublingProcess.Observation)
    (post : doubling.Post () () before after)
    (step : doublingProcess.Step before (.external .wake) after issued emitted) :
    issued = 0 ∧ emitted = [] :=
  doublingCollapses.issues_nothing trivial post step

/-- **And a caller holding the collapse knows which answer runs.** -/
theorem the_collapse_runs_the_selection (before : Cell)
    {finish : doublingCollapses.source.Machine} {exitState : doubling.ExitState}
    (steps : doublingCollapses.source.InternalSteps
      (doublingCollapses.source.enter () before) finish)
    (atExit : doublingCollapses.source.decide finish = .exit exitState) :
    doublingCollapses.source.read finish = doublingCollapses.behavior.after () before :=
  (doublingCollapses.answer_is_the_selection trivial steps atExit).2

/-! ## And the one that must not collapse -/

/--
A blocking read: the buffer ends up holding however many bytes arrived.

Every field is satisfiable, and the footprint is not degenerate — the second
component genuinely does not move. What is wrong with it is `Post`, which
relates one before-state to a different after-state for every byte count, and
lets the environment pick. That is exactly `docs/PROCESS.md` §3's "waits for
external entropy".
-/
def blockingRead : SerialFunctionContract Cell where
  Input := Unit
  Output := Nat
  Fault := Empty
  ExitState := Unit
  Obligations := Unit
  Resources := Unit
  Pre := fun _ _ => True
  disposition := fun _ => .returned 0
  Post := fun _ _ before after => after.2 = before.2
  obligations := fun _ _ before after => after = before
  resources := fun _ _ before after => after = before
  footprintAgrees := fun before after => before.2 = after.2
  postWithinFootprint := by
    rintro _ _ before after post
    exact post.symm
  footprintSeparates := ⟨(0, 0), (0, 1), by decide⟩
  faultCustody := fun fault _ _ _ _ _ _ => fault.elim
  faultsDeclared := by
    rintro _ _ fault _ _ _ _ _ _ _ _ _ _
    exact fault.elim
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  workBound := none

/-- It really does admit two answers to one call. -/
theorem the_read_can_answer_two_ways :
    blockingRead.Post () () (0, 7) (0, 7) ∧ blockingRead.Post () () (0, 7) (1, 7) :=
  ⟨rfl, rfl⟩

/--
**So no machine realizes it, and it has no collapse.**

The refusal §3 asks for, and it quantifies over every source: there is no
cleverness that makes a blocking read serial. It stays a frontier and gets a
child protocol, which is §3's "a synchronous platform API is still modeled by a
child protocol because its return is external entropy, even when its selected
machine realization is one blocking ABI call".
-/
theorem a_blocking_read_loses_an_answer (behavior : ExactSerialBehavior blockingRead) :
    ∃ after, blockingRead.Post () () (0, 7) after ∧ after ≠ behavior.after () (0, 7) := by
  by_cases picked : behavior.after () (0, 7) = (0, 7)
  · exact ⟨(1, 7), rfl, by rw [picked]; decide⟩
  · exact ⟨(0, 7), rfl, fun same => picked same.symm⟩

/--
**And a collapse of it loses an answer too**, whatever process it is offered to.

`behavior` is a field, so a `CollapsesToOneTransition` for this contract carries
a selection — and by `a_blocking_read_loses_an_answer` some permitted answer is
not the one it selects. That is the frontier argument in the shape
`agent-bus` `g-design:141` leaves available: not that the contract is
unrealizable, but that collapsing it silently discards the answers the
environment was going to supply, which is what makes a blocking read a child
protocol rather than a call.
-/
theorem a_blocking_read_collapse_loses_an_answer
    {Exclusive : blockingRead.Input → doublingProcess.State → Prop} {Point : Type}
    {LinearizesAt Noninterference : Point → blockingRead.Input → doublingProcess.State → Prop}
    {event : ProcessEvent doublingProcess.vocabulary}
    (collapse : CollapsesToOneTransition (p := doublingProcess) blockingRead Exclusive Point
      LinearizesAt Noninterference event) :
    ∃ after, blockingRead.Post () () (0, 7) after ∧
      after ≠ collapse.behavior.after () (0, 7) :=
  a_blocking_read_loses_an_answer collapse.behavior

/-! ## The two layers, and what each one refuses

`agent-bus` `g-design:141`, ruling on `g-auditor:12`. `converse` used to sit
between a source and the *contract*, which made every public `Post`
single-valued. It now sits between a source and an `ExactSerialBehavior`, and a
caller reads the contract through `ExactSerialBehavior.Refines`.

These three fixtures are the acceptance gate the ruling names, and the middle one
is the trap.
-/

/--
**No contract permits everything, and the ruling's constant-true fixture cannot
be built.**

`agent-bus` `g-design:141` names a "constant-false/constant-true shared-contract"
pair as part of its acceptance gate. The constant-false half is below. The
constant-true half **does not exist**, and that is a better answer than the
fixture: `postWithinFootprint` puts every permitted after-state inside the
footprint and `footprintSeparates` says the footprint excludes something, so a
`Post` that holds of every pair would force `footprintAgrees` to hold of every
pair too.

So the two-layer split cannot be abused by pairing a real implementation with a
contract that promises nothing — the contract type already refuses that, and it
refused it before this change. What a caller gets is still exactly the strength
of the `Post` they were given, and `ExactSerialBehavior.Refines` transports that
and no more; but the floor is not zero.
-/
theorem no_contract_permits_everything {State : Type}
    (contract : SerialFunctionContract State)
    (input : contract.Input) (exit : contract.ExitState)
    (permits : ∀ before after, contract.Post input exit before after) : False := by
  obtain ⟨left, right, separated⟩ := contract.footprintSeparates
  exact separated (contract.postWithinFootprint input exit left right (permits left right))

/--
**And a contract permitting nothing is refined by nothing.**

The constant-false end. `forbidding.Pre` holds everywhere and its `Post` holds
nowhere, so no selection can be inside it — the refinement obligation is real at
both ends of the range, which is what makes it a bound rather than a formality.
-/
def forbidding : SerialFunctionContract Cell where
  Input := Unit
  Output := Unit
  Fault := Empty
  ExitState := Unit
  Obligations := Unit
  Resources := Unit
  Pre := fun _ _ => True
  disposition := fun _ => .returned ()
  Post := fun _ _ _ _ => False
  obligations := fun _ _ before after => after = before
  resources := fun _ _ before after => after = before
  footprintAgrees := fun before after => before.2 = after.2
  postWithinFootprint := by intro _ _ _ _ post; exact post.elim
  footprintSeparates := ⟨(0, 0), (0, 1), by decide⟩
  faultCustody := fun fault _ _ _ _ _ _ => fault.elim
  faultsDeclared := by
    rintro _ _ fault _ _ _ _ _ _ _ _ _ _
    exact fault.elim
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  workBound := none

theorem forbidding_is_refined_by_nothing (behavior : ExactSerialBehavior forbidding) :
    ¬ behavior.Refines := by
  intro refines
  exact refines () (0, 0) trivial

/--
**And the blocking read still has no exact behaviour**, which is where the
frontier refusal now lives.

`the_read_can_answer_two_ways` shows `blockingRead.Post` relates one before-state
to two after-states. An `ExactSerialBehavior` selects *one* — `after` is a
function of the input and the before-state — so a selection that refines this
contract exists, and what it cannot do is cover both answers.

That is the honest form of the old refusal. Before `g-design:141` the argument
was that no *source* realizes the contract, obtained by making the contract
single-valued; the cost was that every public contract became single-valued.
Now the contract stays as permissive as §3 allows, and what a `blockingRead`
lacks is a selection that accounts for where the second answer came from — the
external entropy §3 excludes.
-/
theorem no_exact_behavior_covers_both_answers (behavior : ExactSerialBehavior blockingRead) :
    ¬ (behavior.after () (0, 7) = (0, 7) ∧ behavior.after () (0, 7) = (1, 7)) := by
  rintro ⟨first, second⟩
  rw [first] at second
  exact absurd second (by decide)

end Grass.Process.Tests.Serial
