import Grass.Process.Correct

/-!
# A total livelock, and the proof that it is excluded

`spin` consumes one demand and reissues the same demand, forever: the state is
untouched, nothing is emitted, and its vocabulary has no external event at all.
Its run state is bit-for-bit identical after every transition —
`spin_loops` exhibits the cycle and `spin_loop_is_reachable` shows it is not a
statement about an empty class.

This file is here because for one commit `spin` had a full `ProcessCorrect`.

`Grass/Process/Progress.lean`'s `StepProgresses` had gained a demand-result
disjunct that fired on the event's label alone — "an outstanding demand was
answered" — with nothing said about what the step put back. Local adversarial
review built `spin` against it: a constant measure, `Demanded := fun _ => False`
so nothing is degenerate in the permissive direction,
`TerminalRemainderLaw.strict`, and an **empty** `ExternalEvent` so it could not
fall back on the self-delivered-tick escape that module already discloses.
Every field was discharged.

Two things then changed, and both are needed:

* `MeetsProcessProgress.productive` moved to reachable steps with a real
  successor bag, which is what let `countdown`'s unreachable `.result .log` case
  stop being the reason the disjunct was widened in the first place;
* the disjunct itself is gone. `ProcessMeasure.rank` now takes the outstanding
  bag, so answering a demand is progress exactly when the author's own measure
  says the run got smaller.

The first repair of the disjunct kept it and added `issued.card = 0`. That
excludes `spin` and does not exclude `osc` —
`Tests/Process/OscillateFixtures.lean` — which alternates between shrinking the
bag and shrinking the state rank and returns the run to where it started. Two
descent orders in a disjunction are not an order. That is the finding this file
did not catch, and the reason it is worth saying here: a fixture that pins one
attack does not pin the class.

`spin_has_no_progress_record` below is stated for **every** measure and every
invariant true at the state — not for the particular ones the attack used. That
is the form a fixture has to take if it is to notice a future re-widening rather
than a future re-tuning.

## What `spin` still has

`handlesEveryEvent` and `notStuck` are both satisfiable for it, and
`spin_responds` and `spin_is_never_stuck` say so. That is the point of keeping
them: the two responsiveness fields are about a process answering what arrives,
and a livelock answers everything. Responsiveness was never what excluded this,
and a fixture that only refuted the record as a whole would leave a reader
guessing which field did the work.
-/

namespace Grass.Process.Tests.Spin

open Grass.Process

/-! ## The process -/

/-- One demand, one result, and nothing else. `ExternalEvent` is empty on
purpose: `spin` may not appeal to the entropy disjunct. -/
@[reducible] def spinVocabulary : ProcessVocabulary.{0} where
  ExternalEvent := PEmpty
  Demand := Unit
  Result := fun _ => Unit
  Observation := PEmpty
  InterruptReason := PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/-- Answer the demand; issue it again. -/
@[reducible] def spin : ProcessSpec.{0, 0} where
  vocabulary := spinVocabulary
  Request := Unit
  State := Unit
  TerminalResult := PEmpty
  Initial := fun _ state issued emitted =>
    state = () ∧ issued = Bag.ofList [()] ∧ emitted = []
  Terminal := fun _ _ result => result.elim
  Step := fun _ event after issued emitted =>
    match event with
    | .result _ _ => after = () ∧ issued = Bag.ofList [()] ∧ emitted = []
    | .external e => e.elim
    | .interrupted _ reason => reason.elim
    | .fault f => f.elim
    | .environmentViolation v => v.elim
  view := none

/-- Strict in every direction that could otherwise be blamed. -/
@[reducible] def spinAcceptance : ProcessAcceptance spin where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun _ _ => True
  Demanded := fun _ => False
  terminalRemainder := TerminalRemainderLaw.strict spin

/-! ## Two facts about every step it can take -/

theorem spin_step_issues {state after : spin.State} {event : spin.Event}
    {issued : Bag spin.Demand} {emitted : spin.Segment}
    (stepped : spin.Step state event after issued emitted) :
    issued = Bag.ofList [()] := by
  cases event with
  | external e => exact e.elim
  | result _ _ => exact stepped.2.1
  | interrupted _ reason => exact reason.elim
  | fault f => exact f.elim
  | environmentViolation v => exact v.elim

theorem spin_step_settles {state after : spin.State} {event : spin.Event}
    {issued : Bag spin.Demand} {emitted : spin.Segment}
    (stepped : spin.Step state event after issued emitted) :
    event.settles = some () := by
  cases event with
  | external e => exact e.elim
  | result d _ => cases d; rfl
  | interrupted _ reason => exact reason.elim
  | fault f => exact f.elim
  | environmentViolation v => exact v.elim

/-! ## The livelock is reachable -/

/-- A live `spin` always holds its one demand. -/
def SpinLive : ProcessRunState spin () → Prop
  | .running _ outstanding _ => () ∈ outstanding
  | .terminal _ _ _ => True

theorem spin_live {segmented : Segmented spin.Observation}
    {runState : ProcessRunState spin ()}
    (reached : Reachable spinAcceptance.terminalRemainder () segmented runState) :
    SpinLive runState := by
  induction reached with
  | initial isInitial =>
    cases isInitial with
    | running initial => simp [SpinLive, initial.2.1]
  | initialTerminal _ => trivial
  | step _ transition _ _ =>
    cases transition with
    | step settlesNothing stepped =>
      rw [spin_step_settles stepped] at settlesNothing
      simp at settlesNothing
    | settle _ _ stepped =>
      rw [spin_step_issues stepped]
      simp [SpinLive]
    | terminate _ _ => trivial

/-- The initial run state, reached in one `Initial`. -/
theorem spin_loop_is_reachable :
    Reachable spinAcceptance.terminalRemainder () (Segmented.empty.emit [])
      (.running () (Bag.ofList [()]) []) :=
  .initial (.running ⟨rfl, rfl, rfl⟩)

/--
**And the run returns to the identical run state.**

Not merely "does not terminate": state, outstanding bag and trace are all
unchanged, so no measure on any of the three can descend across it. This is what
a progress condition has to exclude, and what one that reads the event's label
does not.
-/
theorem spin_loops (observations : Trace spin.Observation) :
    ProcessRunTransition spinAcceptance.terminalRemainder ()
      (.running () (Bag.ofList [()]) observations)
      (.running () (Bag.ofList [()]) observations) := by
  have step := ProcessRunTransition.settle
    (law := spinAcceptance.terminalRemainder) (request := ())
    (observations := observations) (event := .result () ())
    (demand := ()) (remainder := 0) (by simp) (by rfl)
    (show spin.Step () (.result () ()) () (Bag.ofList [()]) [] from ⟨rfl, rfl, rfl⟩)
  simpa using step

/-! ## What it still satisfies -/

/-- Every event that could arrive has a transition. -/
theorem spin_responds (event : spin.Event) :
    ∃ after issued emitted, spin.Step () event after issued emitted := by
  cases event with
  | external e => exact e.elim
  | result _ _ => exact ⟨(), Bag.ofList [()], [], rfl, rfl, rfl⟩
  | interrupted _ reason => exact reason.elim
  | fault f => exact f.elim
  | environmentViolation v => exact v.elim

/-- And no reachable state is stuck. -/
theorem spin_is_never_stuck {segmented : Segmented spin.Observation}
    {state : spin.State} {outstanding : Bag spin.Demand}
    {observations : Trace spin.Observation}
    (reached : Reachable spinAcceptance.terminalRemainder () segmented
      (.running state outstanding observations)) :
    ∃ event, EventDeliverable outstanding event ∧
      ∃ after issued emitted, spin.Step state event after issued emitted := by
  refine ⟨.result () (), ?_, (), Bag.ofList [()], [], rfl, rfl, rfl⟩
  intro demand _
  cases demand
  exact spin_live reached

/-! ## And what it does not -/

/-- The bag `spin` holds is what it holds again: consume the one occurrence,
issue one back. -/
theorem spin_successor_bag :
    SuccessorBag (p := spin) (Bag.ofList [()]) (.result () ()) (Bag.ofList [()])
      (Bag.ofList [()]) :=
  ⟨0, rfl, by simp⟩

/-- Nothing `spin` emits is demanded. -/
theorem spin_never_observes (segment : spin.Segment) :
    ¬ spinAcceptance.SegmentIsDemanded segment := by
  rintro ⟨_, _, demanded⟩
  exact demanded

/-- So the loop step is a silent step that changes nothing. -/
theorem spin_steps_silently :
    SilentStep spinAcceptance () (Bag.ofList [()]) () (Bag.ofList [()]) :=
  ⟨.result () (), Bag.ofList [()], [], ⟨rfl, rfl, rfl⟩, spin_successor_bag, rfl,
    spin_never_observes _⟩

/--
**The loop step progresses under no measure at all.**

All three disjuncts refuted, and the third is the one that does the work: the
step returns the run to the same state holding the same bag, and a well-founded
order is irreflexive.

Stated for an arbitrary `ProcessMeasure`, which is what makes it a fixture about
`StepProgresses` rather than about a measure someone chose badly. Note that the
statement no longer mentions `issued`: the version of `StepProgresses` this file
was written against had a disjunct about it, and folding that into the measure
is what made this refutation a two-line consequence of well-foundedness instead
of a case analysis on the event.
-/
theorem spin_step_does_not_progress (measure : ProcessMeasure spin) :
    ¬ StepProgresses spinAcceptance measure () (Bag.ofList [()]) ()
      (Bag.ofList [()]) (.result () ()) [] := by
  rintro (⟨entropy, _⟩ | ⟨_, _, demanded⟩ | decreases)
  · exact entropy.elim
  · exact demanded
  · exact measure.not_decreases_self () (Bag.ofList [()]) decreases

/--
**So `spin` has no progress record, whatever measure or invariant is offered.**

`productive` is quantified over reachable steps with a real successor bag, and
this step has both: `spin_loop_is_reachable` supplies the run state and
`spin_successor_bag` consumes the occurrence the bag holds. The invariant is the
caller's, so the statement takes an arbitrary one and the only hypothesis is that
it holds where the loop is — a caller who cannot even claim that has not made a
progress claim about this process.
-/
theorem spin_has_no_progress_record (Invariant : spin.State → Prop)
    (holds : Invariant ()) :
    ¬ Nonempty (MeetsProcessProgress spin spinAcceptance Invariant ()) := by
  rintro ⟨progress⟩
  exact progress.measure.not_decreases_self () (Bag.ofList [()])
    (progress.silent_step_descends spin_loop_is_reachable holds spin_steps_silently)

/--
**And therefore no correctness record either.**

`ProcessCorrect` carries `progress` as a field, so the exclusion propagates
without a separate argument. Worth stating: it is the headline the attack
produced — "this livelock is a correct process" — and it is the sentence that is
now false.
-/
theorem spin_is_not_correct : ¬ Nonempty (ProcessCorrect spin spinAcceptance) := by
  rintro ⟨correct⟩
  exact spin_has_no_progress_record correct.Invariant
    (correct.initial () () (Bag.ofList [()]) [] ⟨rfl, rfl, rfl⟩) ⟨correct.progress ()⟩

end Grass.Process.Tests.Spin
