import Grass.Process.Network.Progress
import Tests.Process.TransitionFixtures

/-!
# What a progress measure has to say to be worth anything

`Grass/Process/Network/Progress.lean` proves that a network cannot return to
where it started by steps that produced no demanded observation and never
paused. That theorem is about the class of `SilentRun`s, and a measure can make
that class empty by declaring every network at a frontier.

This file exhibits exactly that measure, shows it excludes nothing, and shows it
fails `Useful`. The point is not that the degenerate measure is a mistake — it
is a legal value of the type — but that a reader can see which side of the line
any given measure is on, and that the line is drawn somewhere.

`the_receive_adds_no_observation` is the other half: at a measure that declared
`beforeReceive` running, the receive step *is* a silent step, so the class is
not empty for want of steps to put in it.
-/

namespace Grass.Process.Tests.Progress

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.Transition (serverPlan beforeReceive afterReceive receiveAsStep)

/-! ## The degenerate measure -/

/--
Everything is at a frontier, nothing is demanded, and the rank is constant.

A legal `NetworkProgressMeasure`, and `descendsOrProduces` costs nothing: the
third disjunct is `trivial` at every step. That is what makes the next two
theorems worth stating.
-/
def everythingPaused : serverPlan.NetworkProgressMeasure where
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  rankTransitive := fun _ _ _ first second => Nat.lt_trans first second
  rank := fun _ => 0
  demanded := fun _ => False
  AtFrontier := fun _ => True
  descendsOrProduces := fun _ => Or.inr (Or.inr trivial)

/--
**And it excludes nothing.**

No run is silent under it, because every network is paused — so
`no_silent_cycle` is a theorem about an empty class.
-/
theorem everything_paused_excludes_nothing {before after : serverPlan.LogicalProcessNetwork}
    (run : ProcessPlan.NetworkProgressMeasure.SilentRun everythingPaused before after) :
    False := by
  cases run with
  | one _ _ running => exact running trivial
  | more _ _ _ running => exact running trivial

/-- **Which is what `Useful` names.** -/
theorem everything_paused_is_not_useful : ¬ everythingPaused.Useful := by
  rintro ⟨network, running⟩
  exact running trivial

/-! ## And a step that would be silent under a measure that ran anything -/

/--
**The receive adds no observation at all**, so it is silent under every measure
whatever any specification demands.

Stated without a measure and without a demandedness hypothesis, which is
stronger than the form `silent_step_descends` consumes — the unused-variable
linter is what noticed the hypothesis was doing nothing, and the stronger
statement is the true one.

This is the half that shows the class is not empty for want of steps: give a
measure that declares `beforeReceive` running, and the receive goes straight
into a `SilentRun`. What it cannot do is go into one *and* leave the rank alone,
which is the whole content of `descendsOrProduces`.
-/
theorem the_receive_adds_no_observation
    (observation : fixtureBoundary.Observation)
    (present : observation ∈ afterReceive.observations) :
    observation ∈ beforeReceive.observations := by
  have same : beforeReceive.observations = afterReceive.observations :=
    receiveAsStep.transition.touchesOnly .observations (by
      rintro (isEscrow | isSession)
      · exact absurd isEscrow (by simp)
      · exact absurd isSession (by simp))
  rw [same]
  exact present

/--
**So a measure that declares `beforeReceive` running must make the receive
descend.**

`descendsOrProduces` with two of its three disjuncts closed: the receive
produces nothing, and the measure said it was not paused. A measure that wanted
the receive to be free would have to declare `beforeReceive` at a frontier — and
then it is one step closer to `everythingPaused`.
-/
theorem a_running_measure_must_pay_for_the_receive
    (measure : serverPlan.NetworkProgressMeasure)
    (running : ¬ measure.AtFrontier beforeReceive) :
    measure.rankLt (measure.rank afterReceive) (measure.rank beforeReceive) :=
  measure.silent_step_descends receiveAsStep
    (fun observation _ present => the_receive_adds_no_observation observation present)
    running

end Grass.Process.Tests.Progress
