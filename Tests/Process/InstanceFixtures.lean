import Grass.Process.Network.Instance
import Tests.Process.M2GraphFixtures

/-!
# A lifecycle tag that a network cannot lie with

`Grass/Process/Network/Instance.lean` makes one claim that carries the whole
weight of `ProcessLifecycle` having no payload: that `terminated` is a claim
*about the state*, so nothing is lost by leaving the result off the tag.

Two things have to be true for that, and neither is checkable inside the module.

* `LifecycleWitnessed` must have teeth — an instance tagged `terminated` whose
  state is not terminal must fail it. `terminated_at_three_is_not_witnessed`.
* It must not be vacuous the other way — a genuinely finished instance must
  satisfy it and yield its result. `terminated_at_zero_is_witnessed`.

Without the first, `terminated` would be a label a network could apply to a
running process, and `terminated_has_result` would be recovering a result from
nothing. Without the second the predicate would be unsatisfiable and every
terminating run would be unrepresentable.

The protocol is `countdown`: a state is terminal exactly when it has reached
zero, which makes both cases concrete rather than abstract.
-/

namespace Grass.Process.Tests.Instances

open Grass.Process
open Grass.Process.Tests

/-- The listener incarnation this connection was spawned by. -/
def listenerZero : serverTopology.ProcessRef .listener where
  instanceId := ()
  generation := ⟨.processGeneration, 0⟩
  isGeneration := rfl

/-- A connection incarnation, mid-countdown at three. -/
def counting : ProcessInstance serverTopology where
  kind := .connection
  ref := connectionSeven 0
  parent := some ⟨.listener, listenerZero⟩
  request := ⟨3⟩
  localState := ⟨3⟩
  lifecycle := .running

/-- The same incarnation, finished. -/
def finished : ProcessInstance serverTopology :=
  { counting with localState := ⟨0⟩, lifecycle := .terminated }

/-- And the lie: tagged terminated while still counting. -/
def lying : ProcessInstance serverTopology :=
  { counting with lifecycle := .terminated }

/-! ## The tag is a claim about the state -/

/--
**A running process cannot be tagged terminated.**

The teeth. `lying` differs from `counting` only in its tag, and that is enough
to make it not witnessed — so a network carrying `LifecycleWitnessed` cannot
contain it.
-/
theorem terminated_at_three_is_not_witnessed : ¬ lying.LifecycleWitnessed := by
  intro witnessed
  obtain ⟨_, terminal⟩ := witnessed rfl
  have counted : ¬ ((3 : Nat) = 0) := by decide
  exact counted terminal

/-- A genuinely finished process is witnessed, so the predicate is satisfiable. -/
theorem terminated_at_zero_is_witnessed : finished.LifecycleWitnessed :=
  fun _ => ⟨⟨()⟩, rfl⟩

/--
And the result comes back out, which is the whole argument for the payload-free
tag: nothing was dropped when `terminated` was chosen over a constructor
carrying a `TerminalResult`.
-/
theorem finished_yields_its_result :
    ∃ result, (serverTopology.protocol finished.kind).Terminal
      finished.request finished.localState result :=
  finished.terminated_has_result terminated_at_zero_is_witnessed rfl

/-- A running process is witnessed vacuously, and is not thereby terminal. -/
theorem counting_is_witnessed : counting.LifecycleWitnessed :=
  ProcessInstance.live_witnessed_vacuously trivial

/-! ## Liveness -/

/-- A cancelling process is running, so it is live. -/
theorem counting_is_live : counting.Live := trivial

/-- A finished one is not. -/
theorem finished_is_not_live : ¬ finished.Live := fun live => live

/-!
### There is no state between running and the four terminal ones

The negative fixture for the enumeration. If anyone adds a `cancelling`
constructor — the one this module's note argues against, because a cancelling
process still steps — this `#guard_msgs` stops matching and the file fails.
`detached` is here for the same reason on the other side: `detach` changes
`parent`, not liveness, so a detached child is still running.
-/
/--
error: Unknown constant `Grass.Process.ProcessLifecycle.cancelling`

Note: Inferred this name from the expected resulting type of `.cancelling`:
  ProcessLifecycle
-/
#guard_msgs in
example : ProcessLifecycle := .cancelling

/--
error: Unknown constant `Grass.Process.ProcessLifecycle.detached`

Note: Inferred this name from the expected resulting type of `.detached`:
  ProcessLifecycle
-/
#guard_msgs in
example : ProcessLifecycle := .detached

/-! ## Parenthood -/

/-- The connection has a parent, so it is not a root. -/
theorem counting_is_not_root : ¬ counting.IsRoot := by
  intro isRoot
  exact absurd isRoot (by simp [ProcessInstance.IsRoot, counting])

end Grass.Process.Tests.Instances
