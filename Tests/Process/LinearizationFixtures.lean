import Grass.Process.Trace.Linearization
import Tests.Process.TransitionFixtures

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

/--
**A step independent of the receive still cannot be told apart by the trace.**

The receive is silent, so whichever side of it an emission happened, the trace
is the same. Stated with the receive as one half because it is the concrete step
this plan has.
-/
theorem nothing_independent_of_the_receive_is_disturbed_by_it
    {c d : serverPlan.LogicalProcessNetwork}
    {other : serverPlan.NetworkTransition c d}
    (independent : receiveStep.Independent other) :
    beforeReceive.observations = afterReceive.observations ∨
      c.observations = d.observations :=
  ProcessPlan.one_of_two_independent_steps_is_silent independent

end Grass.Process.Tests.Linearization
