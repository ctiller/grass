import Grass.Process.Network.Progress
import Tests.Process.TransitionFixtures

/-!
# What a progress measure has to say to be worth anything

`Grass/Process/Network/Progress.lean` proves that no infinite run of silent,
off-frontier steps exists. That theorem is about the class of `SilentRun`s, and
the obvious way to make the class empty is to declare every network at a
frontier.

`frontierIsExternal` is what stops that, and this file is the check. A network a
non-entropy step can leave is not at a frontier, so at the M2 fixture plan
`beforeReceive` is provably running under *every* measure — the degenerate
measure is not merely bad practice, it is unconstructible.

An earlier version of this file exhibited the all-paused measure and showed it
failed `Useful`. Local adversarial review pointed out that `Useful` separates
that measure from nothing else: a measure can declare one network running and
pause the rest, and every theorem is still about an empty class. The field
replaced the predicate, and the fixture changed shape with it.
-/

namespace Grass.Process.Tests.Progress

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.Transition (serverPlan beforeReceive afterReceive receiveAsStep
  receiveStep)

/-! ## Why the receive is silent -/

/--
**The receive emits nothing at all**, so it is silent under every measure
whatever any specification demands.

Stated without a measure and without a demandedness hypothesis, which is
stronger than the form `silent_step_descends` consumes — the unused-variable
linter is what noticed the hypothesis was doing nothing, and the stronger
statement is the true one.
-/
theorem the_receive_emits_nothing
    (emitted : List fixtureBoundary.Observation)
    (appended : afterReceive.observations = beforeReceive.observations ++ emitted) :
    emitted = [] := by
  have same : beforeReceive.observations = afterReceive.observations :=
    receiveAsStep.transition.touchesOnly .observations (by
      rintro (isEscrow | isSession)
      · exact absurd isEscrow (by simp)
      · exact absurd isSession (by simp))
  rw [← same] at appended
  have lengths := congrArg List.length appended
  simp only [List.length_append] at lengths
  exact List.eq_nil_of_length_eq_zero (by omega)

/-! ## And why no measure may call it paused -/

/--
**The receive is not driven by entropy.**

A message crossing a channel between two processes of this network is the
network acting on itself. `docs/PROCESS.md` §7's frontier is where the *outside*
world has to act, and nothing outside has to act for this receive to happen.
-/
theorem the_receive_is_not_entropy : ¬ receiveStep.DrivenByEntropy := id

/--
**So no measure can declare `beforeReceive` at a frontier.**

`frontierIsExternal` at a concrete network, and the reason the all-paused
measure is gone from this file: a measure that paused everything would have to
claim the outside world was needed for a receive between two processes of the
program.

Quantified over every measure, which is the form that matters — this is not a
fact about one badly chosen measure but about the type.
-/
theorem nothing_pauses_beforeReceive (measure : serverPlan.NetworkProgressMeasure) :
    ¬ measure.AtFrontier beforeReceive :=
  fun paused => the_receive_is_not_entropy (measure.frontierIsExternal paused receiveAsStep)

/-- **And so every measure is `Useful`**, rather than being asked to be. -/
theorem every_measure_is_useful (measure : serverPlan.NetworkProgressMeasure) :
    measure.Useful :=
  ⟨beforeReceive, nothing_pauses_beforeReceive measure⟩

/-! ## What that costs a measure -/

/--
**The receive is a silent run, under any measure at all.**

Half the non-vacuity: `no_infinite_silent_run` is about a class this plan can
put something in. What it cannot put in is an *infinite* sequence of them, which
is the theorem.
-/
theorem the_receive_is_a_silent_run (measure : serverPlan.NetworkProgressMeasure) :
    ProcessPlan.NetworkProgressMeasure.SilentRun measure beforeReceive afterReceive :=
  .one receiveAsStep
    (fun emitted observation appended _ present => by
      rw [the_receive_emits_nothing emitted appended] at present
      exact absurd present (by simp))
    (nothing_pauses_beforeReceive measure)

/--
**And therefore every measure must pay for it.**

`descendsOrProduces` with two of its three disjuncts closed by theorems rather
than by hypotheses: the receive produces nothing, and no measure may call
`beforeReceive` paused. So the rank descends across it, under every measure,
with no hypothesis left for a measure to wriggle out through.

An earlier version took `¬ measure.AtFrontier beforeReceive` as a hypothesis,
and the review's question was whether any measure could satisfy it. It is now a
theorem.
-/
theorem every_measure_pays_for_the_receive (measure : serverPlan.NetworkProgressMeasure) :
    measure.rankLt (measure.rank afterReceive) (measure.rank beforeReceive) :=
  measure.silent_run_descends (the_receive_is_a_silent_run measure)

end Grass.Process.Tests.Progress
