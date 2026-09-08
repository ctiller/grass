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
  converse := by
    rintro _ before _ after _ rfl
    exact ⟨doubled before, doubling_runs before, doubling_decides_at_exit before, rfl⟩
  bounded := by
    rintro bound isSome input before _
    injection isSome with same
    subst same
    exact ⟨doubled before,
      .step (doubling_decides_at_entry before) (.refl 0 _),
      by rw [doubling_decides_at_exit before]; trivial⟩

/-- **So the answer is determined, and the routine really is serial.** -/
theorem doubling_answer_is_determined (before left right : Cell)
    (leftPost : doubling.Post () () before left)
    (rightPost : doubling.Post () () before right) : left = right :=
  doubling_is_realized.post_is_determined trivial leftPost rightPost

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

/-- **And a caller holding the collapse holds the determinacy.** -/
theorem the_answer_is_determined (before left right : Cell)
    (leftPost : doubling.Post () () before left)
    (rightPost : doubling.Post () () before right) : left = right :=
  doublingCollapses.answer_is_determined trivial leftPost rightPost

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
theorem a_blocking_read_has_no_realizing_source
    (source : SerialFunctionSource blockingRead)
    (realizes : SerialFunctionRealizes blockingRead source) : False :=
  realizes.a_call_that_can_answer_two_ways_is_not_serial trivial
    the_read_can_answer_two_ways.1 the_read_can_answer_two_ways.2 (by decide)

/--
**And therefore no collapse, whatever process it is offered to.**

`source` and `realizes` are fields, so a `CollapsesToOneTransition` for this
contract carries a realizing machine — and there is none. Before those fields
existed this was constructible.
-/
theorem a_blocking_read_does_not_collapse
    {Exclusive : blockingRead.Input → doublingProcess.State → Prop} {Point : Type}
    {LinearizesAt Noninterference : Point → blockingRead.Input → doublingProcess.State → Prop}
    {event : ProcessEvent doublingProcess.vocabulary}
    (collapse : CollapsesToOneTransition (p := doublingProcess) blockingRead Exclusive Point
      LinearizesAt Noninterference event) : False :=
  a_blocking_read_has_no_realizing_source collapse.source collapse.realizes

end Grass.Process.Tests.Serial
