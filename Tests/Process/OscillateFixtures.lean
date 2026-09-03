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
emission disjunct), `TerminalResult := PEmpty` (it never terminates),
`TerminalRemainderLaw.strict`.

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

/-! ## Why it is excluded -/

/-- Nothing `osc` emits is demanded. -/
theorem osc_never_observes (segment : osc.Segment) :
    ¬ oscAcceptance.SegmentIsDemanded segment := by
  rintro ⟨_, _, demanded⟩
  exact demanded

/--
**`osc` has no progress record, whatever measure or invariant is offered.**

Both steps are reachable and neither can use the entropy or emission disjunct,
so `productive` must supply a measure descent across each. Those two descents run
in opposite directions between the same pair of running configurations, which
`ProcessMeasure.not_decreases_both_ways` forbids.

The invariant is the caller's, so the statement takes an arbitrary one and asks
only that it hold at the two states the cycle visits — which `ProcessCorrect`
forces anyway, since `preserved` carries an invariant across every step from an
initial state.
-/
theorem osc_has_no_progress_record (Invariant : osc.State → Prop)
    (atFalse : Invariant false) (atTrue : Invariant true) :
    ¬ Nonempty (MeetsProcessProgress osc oscAcceptance Invariant ()) := by
  rintro ⟨progress⟩
  have out := progress.productive _ false one [] true two (.result () ()) two []
    osc_start_reachable atFalse osc_expand_bag osc_expand
  have back := progress.productive _ true two [] false one (.result () ()) 0 []
    osc_expanded_reachable atTrue osc_contract_bag osc_contract
  rcases out with ⟨entropy, _⟩ | demanded | descends
  · exact entropy.elim
  · exact osc_never_observes _ demanded
  rcases back with ⟨entropy, _⟩ | demanded | climbs
  · exact entropy.elim
  · exact osc_never_observes _ demanded
  exact progress.measure.not_decreases_both_ways descends climbs

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
