import Grass.Process.Network.Progress
import Tests.Process.TransitionFixtures

/-!
# What a progress measure has to say to be worth anything

`Grass/Process/Network/Progress.lean` proves that no infinite run of silent,
off-frontier steps exists. That theorem is about the class of `SilentRun`s, and
the obvious way to make the class empty is to declare every network at a
frontier.

There is no way to make the class empty any more, and this file is what is left
of three rounds of trying to say so.

`AtFrontier` was a field of the measure, with an obligation attached. Reviewers
took both versions apart: "a frontier is left only by entropy" made the predicate
empty for every measure, because a commit or a spawn is enabled almost everywhere
and neither is entropy; adding a rank disjunct then let a measure declare *every*
network paused and empty the `SilentRun` class instead. A frontier is not
something a measure declares — it is a fact about which steps are enabled — so
`ProcessPlan.AtFrontier` is a definition and `descendsOrProduces` asks the
per-step question directly: *was this step the outside acting?*

What is left here is one honest fact about the M2 plan, and it is now one line:
a receive between two processes of the program is not the outside acting and
produces nothing, so every measure pays rank for it.

**What it still owes.** `every_measure_pays_for_the_receive` takes
`reached : measure.Reachable beforeReceive` as a hypothesis, and `beforeReceive`
holds no incarnation of any kind — so it is in no `plan.StepsTo start` for any
start, and the hypothesis is satisfiable only by a measure whose `Reachable` is
strictly wider than reachability. `Grass/Process/Network/Progress.lean`'s index
permits that and does not require it; a reviewer proved the emptiness.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.67 records what this file is worth
until `serverPlan` has a start and a measure.
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
**Nothing pauses this receive**, because a frontier is not a measure's to
declare.

`ProcessPlan.AtFrontier` is "only the outside can move this network", and
`beforeReceive` is not such a network: `receiveStep` moves it and a receive
between two processes of the program is not the outside acting.
-/
theorem beforeReceive_is_not_a_frontier : ¬ serverPlan.AtFrontier beforeReceive :=
  fun paused => the_receive_is_not_entropy (paused receiveAsStep)

/-- **So the M2 plan is `Useful`** — it has a network the program itself can
move. A fact about the plan, not about anyone's measure. -/
theorem the_server_plan_is_useful : serverPlan.Useful :=
  ⟨beforeReceive, beforeReceive_is_not_a_frontier⟩

/-! ## What that costs a measure -/

/--
**The receive is a silent run of every measure that can reach it.**

Half the non-vacuity: `no_infinite_silent_run` is about a class this plan can put
something in. What it cannot put in is an *infinite* sequence of them, which is
the theorem.

The `¬ AtFrontier` hypothesis this used to carry is gone with the field: a silent
run's steps are silent because *they* are not entropy-driven, which no measure
can declare away.
-/
theorem the_receive_is_a_silent_run {start : serverPlan.LogicalProcessNetwork}
    (measure : serverPlan.NetworkProgressMeasure start)
    (reached : measure.Reachable beforeReceive) :
    ProcessPlan.NetworkProgressMeasure.SilentRun measure beforeReceive afterReceive :=
  .one receiveAsStep reached
    (fun emitted observation appended _ present => by
      rw [the_receive_emits_nothing emitted appended] at present
      exact absurd present (by simp))
    the_receive_is_not_entropy

/--
**And every measure pays for it.**

`descendsOrProduces` with two of its three disjuncts closed by theorems rather
than by hypotheses: the receive is not the outside acting, and it produces
nothing. So the rank descends across it, under every measure that can reach it,
with no hypothesis left for a measure to wriggle out through.

Three rounds ago this needed a case analysis on whether the measure paused the
network, and two rounds ago it needed a `¬ AtFrontier` hypothesis that no measure
in the corpus could supply. Removing the field removed both.
-/
theorem every_measure_pays_for_the_receive {start : serverPlan.LogicalProcessNetwork}
    (measure : serverPlan.NetworkProgressMeasure start)
    (reached : measure.Reachable beforeReceive) :
    measure.rankLt (measure.rank afterReceive) (measure.rank beforeReceive) :=
  measure.silent_run_descends (the_receive_is_a_silent_run measure reached)

end Grass.Process.Tests.Progress
