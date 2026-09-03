import Grass.Process.Correct

/-!
# Two descent orders are not an order

`osc` is the process that broke the four-disjunct `StepProgresses`, and it broke
it in a way `Tests/Process/SpinFixtures.lean` could not notice.

`spin` is a livelock that descends in *nothing*. The repair for it — requiring a
settling step to issue nothing before the demand-result disjunct fires — is
correct about `spin` and misses the real problem, which is that
`StepProgresses` then offered **two independent well-founded orders in a
disjunction**: the outstanding bag's cardinality, and a rank on `p.State`. A
disjunction of two orders is not an order, and a process that alternates between
them descends in each on alternate steps while returning to exactly where it
started.

`osc` alternates. From `false` it answers its demand and issues **two**, so the
bag grows — but the state rank falls, and the measure disjunct fires. From `true`
it answers its demand and issues **none**, so the bag shrinks and the
demand-result disjunct fires, leaving the rank free to climb back. `osc_cycles`
exhibits the two steps returning the run state bit-for-bit, and `osc` had a full
`ProcessCorrect`.

Everything else about it is strict, so nothing else can be blamed:
`ExternalEvent := PEmpty` (no entropy escape), `Demanded := fun _ => False` (no
emission disjunct), `TerminalResult := PEmpty` (it never terminates). The
`TerminalRemainderLaw.strict` in `oscAcceptance` is inert rather than strict —
with an empty `TerminalResult` the law is never consulted — and saying so is the
point of this paragraph.

And `osc` is excluded by `productive` alone, not by being stuck:
`osc_responds` and `osc_is_never_stuck` say so. That separation is what
`Tests/Process/SpinFixtures.lean` calls for and what an earlier version of this
file did not have — refuting the record as a whole leaves a reader guessing which
field did the work.

## The repair, and why it is the definition rather than a fixture

`ProcessMeasure.rank` now takes the outstanding bag, and `StepProgresses` is back
to §7's three disjuncts. There is one order over `(state, outstanding)`, so
`ProcessMeasure.not_decreases_both_ways` — well-founded orders are asymmetric —
kills the cycle directly. `osc_has_no_progress_record` below is that argument,
for **every** measure and every invariant true at the two states.

Neither `spin` nor `osc` would be excluded by pinning the other. That is the
reason both are kept.
-/

namespace Grass.Process.Tests.Oscillate

open Grass.Process

/-! ## The process -/

/-- One demand, one result, and no way out. -/
@[reducible] def oscVocabulary : ProcessVocabulary.{0} where
  ExternalEvent := PEmpty
  Demand := Unit
  Result := fun _ => Unit
  Observation := PEmpty
  InterruptReason := PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/--
Answer the demand and issue two; answer it again and issue none.

The two branches are the two disjuncts. Neither step is progress and each was
accepted by a different clause.
-/
@[reducible] def osc : ProcessSpec.{0, 0} where
  vocabulary := oscVocabulary
  Request := Unit
  State := Bool
  TerminalResult := PEmpty
  Initial := fun _ state issued emitted =>
    state = false ∧ issued = Bag.ofList [()] ∧ emitted = []
  Terminal := fun _ _ result => result.elim
  Step := fun state event after issued emitted =>
    match event with
    | .result _ _ =>
        emitted = [] ∧
          (if state then after = false ∧ issued = 0
           else after = true ∧ issued = Bag.ofList [(), ()])
    | .external e => e.elim
    | .interrupted _ reason => reason.elim
    | .fault f => f.elim
    | .environmentViolation v => v.elim
  view := none

/-- Strict in every direction that could otherwise be blamed. -/
@[reducible] def oscAcceptance : ProcessAcceptance osc where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun _ _ => True
  Demanded := fun _ => False
  terminalRemainder := TerminalRemainderLaw.strict osc

/-! ## The two configurations, and the two steps between them -/

/-- One occurrence outstanding. -/
def one : Bag osc.Demand := Bag.ofList [()]

/-- Two. -/
def two : Bag osc.Demand := Bag.ofList [(), ()]

/-- Expanding: from `false`, answer and issue two. -/
theorem osc_expand : osc.Step false (.result () ()) true two [] :=
  ⟨rfl, rfl, rfl⟩

/-- Contracting: from `true`, answer and issue none. -/
theorem osc_contract : osc.Step true (.result () ()) false 0 [] :=
  ⟨rfl, rfl, rfl⟩

/-- The bag after expanding: consume the one held, put two back. -/
theorem osc_expand_bag :
    SuccessorBag (p := osc) one (.result () ()) two two :=
  ⟨0, rfl, by simp⟩

/-- And after contracting: consume one of the two, put none back. -/
theorem osc_contract_bag :
    SuccessorBag (p := osc) two (.result () ()) 0 one :=
  ⟨one, rfl, by simp⟩

/-! ## The cycle is reachable, and it closes -/

theorem osc_start_reachable :
    Reachable oscAcceptance.terminalRemainder () (Segmented.empty.emit [])
      (.running false one []) :=
  .initial (.running ⟨rfl, rfl, rfl⟩)

/-- Answering from `false` reaches the expanded run state. -/
theorem osc_step_out (observations : Trace osc.Observation) :
    ProcessRunTransition oscAcceptance.terminalRemainder ()
      (.running false one observations) (.running true two observations) := by
  have stepped := ProcessRunTransition.settle
    (law := oscAcceptance.terminalRemainder) (request := ())
    (observations := observations) (event := .result () ())
    (demand := ()) (remainder := 0) rfl (show one = Bag.cons () 0 from rfl) osc_expand
  simpa [two] using stepped

/-- The expanded run state is reachable, so the second step is not about an
empty class. -/
theorem osc_expanded_reachable :
    Reachable oscAcceptance.terminalRemainder () ((Segmented.empty.emit []).emit [])
      (.running true two []) :=
  .step osc_start_reachable (osc_step_out []) rfl

/--
**And answering from `true` returns the run to where it started.**

State, outstanding bag and trace are all back. Not "does not terminate" — the
identical run state, after two transitions.
-/
theorem osc_cycles (observations : Trace osc.Observation) :
    ProcessRunTransition oscAcceptance.terminalRemainder ()
      (.running true two observations) (.running false one observations) := by
  have stepped := ProcessRunTransition.settle
    (law := oscAcceptance.terminalRemainder) (request := ())
    (observations := observations) (event := .result () ())
    (demand := ()) (remainder := one) rfl (show two = Bag.cons () one from rfl) osc_contract
  simpa using stepped

/-! ## What it still satisfies -/

/-- Every event it could be handed has a transition. -/
theorem osc_responds (state : osc.State) (event : osc.Event) :
    ∃ after issued emitted, osc.Step state event after issued emitted := by
  cases event with
  | external e => exact e.elim
  | result _ _ =>
    cases state with
    | false => exact ⟨true, two, [], rfl, rfl, rfl⟩
    | true => exact ⟨false, 0, [], rfl, rfl, rfl⟩
  | interrupted _ reason => exact reason.elim
  | fault f => exact f.elim
  | environmentViolation v => exact v.elim

/--
And neither configuration of the cycle is stuck.

Stated at the two configurations the cycle visits, which are the ones
`osc_has_no_progress_record` is about. A `.result` is deliverable at each because
each holds at least one occurrence.
-/
theorem osc_is_never_stuck :
    (∃ event, EventDeliverable one event ∧
        ∃ after issued emitted, osc.Step false event after issued emitted) ∧
      (∃ event, EventDeliverable two event ∧
        ∃ after issued emitted, osc.Step true event after issued emitted) := by
  refine ⟨⟨.result () (), ?_, true, two, [], rfl, rfl, rfl⟩,
    ⟨.result () (), ?_, false, 0, [], rfl, rfl, rfl⟩⟩
  · exact eventDeliverable_of_successorBag osc_expand_bag
  · exact eventDeliverable_of_successorBag osc_contract_bag

/-! ## Why it is excluded -/

/-- Nothing `osc` emits is demanded. -/
theorem osc_never_observes (segment : osc.Segment) :
    ¬ oscAcceptance.SegmentIsDemanded segment := by
  rintro ⟨_, _, demanded⟩
  exact demanded

/-- The expanding step is silent: no entropy in the vocabulary, nothing emitted. -/
theorem osc_expands_silently : SilentStep oscAcceptance false one true two :=
  ⟨.result () (), two, [], osc_expand, osc_expand_bag, rfl, osc_never_observes _⟩

/-- And so is the contracting one. -/
theorem osc_contracts_silently : SilentStep oscAcceptance true two false one :=
  ⟨.result () (), 0, [], osc_contract, osc_contract_bag, rfl, osc_never_observes _⟩

/--
**`osc` has no progress record, whatever measure or invariant is offered.**

An instance of `MeetsProcessProgress.no_silent_two_cycle` rather than an argument
of its own — which is the point of having that theorem. Both steps are reachable
and silent, and two silent descents between the same pair of running
configurations run in opposite directions, which a well-founded order forbids.

An earlier version of this proof did the case analysis inline, over the four
disjuncts `StepProgresses` then had. That version would have kept compiling
across a re-widening that admitted a *different* cycle; this one is the same
theorem the module now states for every process.

The invariant is the caller's, so the statement takes an arbitrary one and asks
only that it hold at the two states the cycle visits — which `ProcessCorrect`
forces anyway, since `preserved` carries an invariant across every step from an
initial state.
-/
theorem osc_has_no_progress_record (Invariant : osc.State → Prop)
    (atFalse : Invariant false) (atTrue : Invariant true) :
    ¬ Nonempty (MeetsProcessProgress osc oscAcceptance Invariant ()) := by
  rintro ⟨progress⟩
  exact progress.no_silent_two_cycle osc_start_reachable osc_expanded_reachable
    atFalse atTrue osc_expands_silently osc_contracts_silently

/--
**And therefore no correctness record either.**

The sentence the attack produced — "this livelock is a correct process" — and
the one that is now false. The invariant hypotheses are discharged from
`ProcessCorrect`'s own fields: `initial` at `false`, and `preserved` across the
expanding step.
-/
theorem osc_is_not_correct : ¬ Nonempty (ProcessCorrect osc oscAcceptance) := by
  rintro ⟨correct⟩
  have atFalse : correct.Invariant false :=
    correct.initial () false one [] ⟨rfl, rfl, rfl⟩
  have atTrue : correct.Invariant true :=
    correct.preserved false true (.result () ()) two [] atFalse osc_expand
  exact osc_has_no_progress_record correct.Invariant atFalse atTrue ⟨correct.progress ()⟩

end Grass.Process.Tests.Oscillate
