import Grass.Process.Correct
import Tests.Process.M1Fixtures

/-!
# A process that is actually correct

`Tests/Process/M1Fixtures.lean` exercises the run relation. Nothing there builds
a `ProcessCorrect` or a `MeetsProcessProgress`, and that gap let a real defect
survive three review rounds: `handlesEveryEvent` and `terminalNoStep`
contradicted each other for every process that terminates, so `ProcessCorrect`
was uninhabited and no fixture noticed.

So this module inhabits them. `oneShot` is the smallest process that terminates
after doing something: it starts working, one event finishes it, and no
transition leaves the finished state.

The point is not the process. The point is that these two records have a witness
at all, and that adding a field to either one has to keep having one.
-/

namespace Grass.Process.Tests

open Grass.Process

/-! ## A process with no demands -/

/--
The vocabulary: one external event, no demands, no faults.

`PEmpty` for `Demand` makes the outstanding bag trivially empty, which is what
keeps the terminal classification in this fixture about the *shape* of the
obligation rather than about arithmetic. `M1Fixtures` covers the counting.
-/
@[reducible] def oneShotVocabulary : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := Unit
  InterruptReason := PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/-- Every bag over an uninhabited demand type is empty. -/
theorem bag_of_pempty_eq_zero (bag : Bag PEmpty.{1}) : bag = 0 := by
  induction bag using Quotient.inductionOn with
  | _ elements =>
    cases elements with
    | nil => rfl
    | cons head _ => exact head.elim

/--
`false` is working, `true` is finished. One event moves it, and nothing moves it
afterwards — which is what `terminalNoStep` needs and what an unguarded law-5
obligation made impossible.
-/
@[reducible] def oneShot : ProcessSpec.{0, 0} where
  vocabulary := oneShotVocabulary
  Request := Unit
  State := Bool
  TerminalResult := Unit
  Initial := fun _ state issued emitted =>
    state = false ∧ issued = 0 ∧ emitted = []
  Terminal := fun _ state _ => state = true
  Step := fun state _ after issued emitted =>
    state = false ∧ after = true ∧ issued = 0 ∧ emitted = []
  view := none

/-- The strictest terminal law: this process may only finish holding nothing. -/
@[reducible] def oneShotRemainder : TerminalRemainderLaw oneShot :=
  TerminalRemainderLaw.strict oneShot

/-- An acceptance that constrains the terminal remainder and nothing else. -/
@[reducible] def oneShotAcceptance : ProcessAcceptance oneShot where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun _ _ => True
  Demanded := fun _ => False
  terminalRemainder := oneShotRemainder

/-! ## It progresses -/

/-- The measure: one step of work remains while the state is `false`. -/
@[reducible] def oneShotMeasure : ProcessMeasure oneShot where
  Rank := Nat
  lt := Nat.lt
  wellFounded := Nat.lt_wfRel.wf
  rank := fun state => if state then 0 else 1

/--
`oneShot` meets its progress contract.

`handlesEveryEvent` is discharged from the non-terminality guard: a state that
is not terminal is `false`, and from `false` every event steps. Without the
guard this field would ask for a step from `true`, which `oneShotCorrect`'s
`terminalNoStep` forbids, and neither record would have a witness.
-/
def oneShotProgress (request : Unit) :
    MeetsProcessProgress oneShot oneShotAcceptance (fun _ => True) request where
  measure := oneShotMeasure
  handlesEveryEvent := by
    rintro _ state _ _ _ _ notTerminal
    intro _
    refine ⟨true, 0, [], ?_, rfl, rfl, rfl⟩
    cases state with
    | false => rfl
    | true => exact absurd ⟨(), rfl⟩ notTerminal
  notStuck := by
    rintro _ state outstanding _ _
    cases state with
    | false =>
      refine Or.inr ⟨.external (), ?_, true, 0, [], rfl, rfl, rfl, rfl⟩
      exact eventDeliverable_of_settles_none (by simp)
    | true =>
      refine Or.inl ⟨(), rfl, ⟨?_⟩⟩
      rw [bag_of_pempty_eq_zero outstanding]
      exact TerminalDemandClassification.empty oneShotRemainder request true ()
        ⟨rfl, rfl, rfl⟩
  productive := by
    rintro state after _ _ _ _ ⟨working, finished, _, _⟩
    subst working; subst finished
    refine Or.inr (Or.inr ?_)
    show (0 : Nat) < 1
    omega

/-! ## It is correct -/

/--
`oneShot` is correct, with a trivial invariant.

Every field is discharged, and two of them are the ones that matter.
`terminalNoStep` holds because `Step` requires `state = false` and `Terminal`
says `state = true`. `progress` holds because `handlesEveryEvent` is guarded by
non-terminality — the two would otherwise be contradictory, which is the defect
this module exists to catch.
-/
def oneShotCorrect : ProcessCorrect oneShot oneShotAcceptance where
  Invariant := fun _ => True
  initial := by intros; trivial
  initialDemands := by intros; trivial
  preserved := by intros; trivial
  demandsWellFormed := by intros; trivial
  terminal := by intros; trivial
  terminalNoStep := by
    rintro _ state _ _ _ _ _ isTerminal ⟨working, _⟩
    rw [isTerminal] at working
    exact absurd working (by decide)
  viewAccepts := by
    intro facet hasView
    exact absurd hasView (by simp [oneShot])
  observationsAccept := by intros; trivial
  progress := oneShotProgress

/--
And the correctness proof composes: every reachable state satisfies the
invariant, by the generic induction rather than by anything written here.
-/
theorem oneShot_invariant_holds {segmented : Segmented Unit}
    {runState : ProcessRunState oneShot ()}
    (reached : Reachable oneShotRemainder () segmented runState) :
    oneShotCorrect.Invariant runState.state :=
  oneShotCorrect.invariant_of_reachable reached

/--
**No reachable running state of `oneShot` is stuck.**

The theorem the two responsiveness fields exist for, instantiated. Before the
guard on `handlesEveryEvent` this statement was vacuously available, because
`oneShotCorrect` could not be built at all.
-/
theorem oneShot_never_stuck {segmented : Segmented Unit} {state : Bool}
    {outstanding : Bag PEmpty.{1}} {observations : Trace Unit}
    (reached : Reachable oneShotRemainder () segmented
      (.running state outstanding observations)) :
    ∃ after, ProcessRunTransition oneShotRemainder ()
      (.running state outstanding observations) after :=
  (oneShotProgress ()).exists_transition reached

/-! ## The trap a partition law can still fall into

Finding from review: the partition conserves occurrences, but `resolved`,
`transferred`, and `pending` are three labels with no independent content, and
the terminating side chooses the partition. A law that constrains only
`pending` therefore bounds nothing — the same occurrences can be called
`resolved`.

`Grass/Process/Spec.lean` says this in prose. Here it is as a theorem, so that
a reader who writes such a law meets the counterexample rather than the warning.
-/

/-- A law that means to allow at most two outstanding demands at termination. -/
@[reducible] def pendingOnly : TerminalRemainderLaw countdown where
  Accepts := fun _ _ _ _ _ pending => pending.card ≤ 2

/--
It bounds nothing: a run holding any number of ticks terminates under it, by
calling all of them `resolved`.
-/
def evadePendingOnly (n : Nat) :
    TerminalDemandClassification pendingOnly 0 0 ()
      (Bag.ofList (List.replicate n Demand.tick)) where
  resolved := Bag.ofList (List.replicate n Demand.tick)
  transferred := 0
  pending := 0
  partition := by simp
  permitted := by simp

theorem pendingOnly_permits_any_number (n : Nat) (observations : Trace Observation) :
    ProcessRunTransition pendingOnly 0
      (.running 0 (Bag.ofList (List.replicate n Demand.tick)) observations)
      (.terminal 0 () observations) :=
  .terminate rfl (evadePendingOnly n)

/--
The law used in `M1Fixtures` does not have that hole, because it pins `resolved`
and `transferred` to zero as well as bounding `pending`.
-/
theorem countdownRemainder_constrains_all_three
    {request state : Nat} {result : Unit}
    {resolved transferred pending : Bag Demand}
    (permitted : countdownRemainder.Accepts request state result resolved
      transferred pending) :
    resolved = 0 ∧ transferred = 0 ∧ pending.card ≤ 2 :=
  ⟨permitted.1, permitted.2.1, permitted.2.2.2⟩

end Grass.Process.Tests
