import Grass.Process.Trace.Linearization
import Tests.Process.CommitFixtures

/-!
# The trace laws at a concrete plan

`Grass/Process/Trace/Linearization.lean` proves two things about every plan:
the observation trace only grows, and two independent steps never both write it.
This file spends both at the M2 fixture plan, where there is an actual step to
apply them to.

The instantiation is the point rather than a formality. `observations_extend` is
proved by cases over all twenty-three constructors, and a case analysis is the
kind of proof that can be *right about every case it lists* while the family it
lists is not the one a consumer meets. Applying it to a step written before it
existed is the check on that.

`the_receive_is_silent` is also a small confirmation that the scope discipline
is doing work in the direction that matters here. The receive was authored with
a scope naming its session and nothing else; that it emits nothing is a
consequence a later module read off the declaration, not a fact its author
stated.
-/

namespace Grass.Process.Tests.Linearization

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.Transition (serverPlan beforeReceive afterReceive receiveAsStep
  receiveStep receive_scope_is_the_session)
open Grass.Process.Tests.Commit (afterBeep quietRunCoalesces beep_is_committed)

/-! ## One concrete step -/

/--
**The receive does not write the trace.**

Read off its declared scope, which names the session fragment and nothing else.
-/
theorem the_receive_is_silent : ¬ receiveStep.Emits := by
  intro emits
  have isSession := (receive_scope_is_the_session _).mp emits
  exact absurd isSession (by simp)

/--
**So the trace is unchanged across it — derived, not asserted.**

`Tests/Process/TransitionFixtures.lean` already proves `observations_did_not_move`
from the fixture's own construction. This proves the same equation from the
general law instead, which is the check worth having: the general law reaches a
step whose author never mentioned it.
-/
theorem the_receive_leaves_the_trace :
    beforeReceive.observations = afterReceive.observations :=
  ProcessPlan.trace_unchanged_of_silent receiveStep the_receive_is_silent

/-! ## The general laws, at this plan -/

/-- Every step of this plan extends the trace. -/
theorem every_step_extends_the_trace {before after : serverPlan.LogicalProcessNetwork}
    (transition : serverPlan.NetworkTransition before after) :
    ∃ emitted, after.observations = before.observations ++ emitted :=
  ProcessPlan.observations_extend transition

/--
**No step of this plan can empty a non-empty trace.**

The consequence a specification stated over observations actually needs, and the
one that would be false if any constructor could rewrite the trace rather than
append to it.
-/
theorem no_step_can_empty_the_trace {before after : serverPlan.LogicalProcessNetwork}
    (transition : serverPlan.NetworkTransition before after)
    (wasObserved : before.observations ≠ []) : after.observations ≠ [] := by
  obtain ⟨emitted, appended⟩ := every_step_extends_the_trace transition
  intro empty
  refine wasObserved ?_
  have lengths := congrArg List.length appended
  rw [empty] at lengths
  simp only [List.length_nil, List.length_append] at lengths
  exact List.eq_nil_of_length_eq_zero (by omega)

/--
**And no execution can, however long.**

Stated over `StepsTo` rather than one step because that is the form a
specification consumes: whatever schedule ran, an observation already made is
still there.
-/
theorem no_execution_can_empty_the_trace {before after : serverPlan.LogicalProcessNetwork}
    (execution : serverPlan.StepsTo before after)
    (wasObserved : before.observations ≠ []) : after.observations ≠ [] := by
  obtain ⟨emitted, appended⟩ := ProcessPlan.execution_observations_extend execution
  intro empty
  refine wasObserved ?_
  have lengths := congrArg List.length appended
  rw [empty] at lengths
  simp only [List.length_nil, List.length_append] at lengths
  exact List.eq_nil_of_length_eq_zero (by omega)

/--
**Two steps of this plan that both write the trace are never independent.**

`docs/FOUNDATION.md` law 18 at this plan: there is no pair of independent
emissions whose order a specification could observe, because there is no pair of
independent emissions.
-/
theorem two_emitting_steps_are_never_independent
    {a b c d : serverPlan.LogicalProcessNetwork}
    {left : serverPlan.NetworkTransition a b} {right : serverPlan.NetworkTransition c d}
    (independent : left.Independent right) (leftEmits : left.Emits) : ¬ right.Emits :=
  fun rightEmits =>
    ProcessPlan.independent_steps_do_not_both_emit independent ⟨leftEmits, rightEmits⟩

/-! ## A step that does emit -/

/--
A commit of a `beep`, as a transition.

`Tests/Process/CommitFixtures.lean` proves the reconciler's side of this; here
it is fed to the `commit` constructor so that the two non-trivial cases of
`observations_extend` are both exercised at a concrete step. Without it nothing
in the corpus had ever satisfied `Emits`, and every theorem about emitting steps
was being checked against an empty case.
-/
def beepCommit : serverPlan.NetworkTransition beforeReceive afterBeep :=
  .commit quietRunCoalesces.committed.observations
    (beep_is_committed.toCommits (by simp [quietRunCoalesces, Grass.Process.Tests.Commit.beeps]))

/-- **And it emits** — the `Emits` predicate is inhabited at this plan. -/
theorem the_commit_emits : beepCommit.Emits :=
  ⟨by simp [quietRunCoalesces, Grass.Process.Tests.Commit.beeps], rfl⟩

/-- **So the trace moved across it**, by the exactness of `Emits`. -/
theorem the_commit_moved_the_trace :
    beforeReceive.observations ≠ afterBeep.observations :=
  (ProcessPlan.emits_iff_the_trace_moved beepCommit).mp the_commit_emits

/-- The commit's own instance of the extension law. -/
theorem the_commit_extends_the_trace :
    ∃ emitted, afterBeep.observations = beforeReceive.observations ++ emitted :=
  ProcessPlan.observations_extend beepCommit

/-- And the receive's, which is the silent case of the same law. -/
theorem the_receive_extends_the_trace :
    ∃ emitted, afterReceive.observations = beforeReceive.observations ++ emitted :=
  ProcessPlan.observations_extend receiveStep

/-- The commit and the receive really are independent: escrow and trace are disjoint. -/
theorem the_commit_and_the_receive_are_independent : beepCommit.Independent receiveStep := by
  intro fragment inCommit inReceive
  obtain ⟨_, isObservations⟩ := inCommit
  rcases (receive_scope_is_the_session fragment).mp inReceive with isEscrow | isSession
  · rw [isEscrow] at isObservations
    exact absurd isObservations (by simp)
  · rw [isSession] at isObservations
    exact absurd isObservations (by simp)

/--
**And nothing independent of the commit may emit.**

The hypothesis is load-bearing here, which it was not in an earlier version of
this fixture: that one concluded a disjunction whose first half was already a
closed theorem, so the independence hypothesis and the other step were both
unused. Local adversarial review caught it.
-/
theorem anything_independent_of_the_commit_is_silent
    {c d : serverPlan.LogicalProcessNetwork}
    {other : serverPlan.NetworkTransition c d}
    (independent : beepCommit.Independent other) : c.observations = d.observations :=
  ProcessPlan.trace_unchanged_of_silent other
    (fun emits => independent .observations the_commit_emits emits)

/-- In particular the receive is, which is the concrete instance. -/
theorem the_receive_is_silent_because_the_commit_emits :
    beforeReceive.observations = afterReceive.observations :=
  anything_independent_of_the_commit_is_silent the_commit_and_the_receive_are_independent

end Grass.Process.Tests.Linearization
