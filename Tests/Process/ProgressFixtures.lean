import Grass.Process.Network.Progress
import Tests.Process.TransitionFixtures

/-!
# What a progress measure has to say to be worth anything

`Grass/Process/Network/Progress.lean` proves that no infinite run of silent,
off-frontier steps exists. That theorem is about the class of `SilentRun`s, and
the obvious way to make the class empty is to declare every network at a
frontier.

`frontierIsExternal` is what charges for that, and this file is the check. A network a
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
**So a measure that pauses `beforeReceive` pays for the receive out of its rank.**

`frontierIsExternal` at a concrete network: a receive between two processes of
the program is not the outside world acting, so the only way to call
`beforeReceive` paused is to show the rank descends across it anyway.

`Reachable beforeReceive` is a hypothesis rather than a fact, and cannot be
anything else here: this file names a world and no start, and
`NetworkProgressMeasure` is now indexed by the network a run begins at. A caller
who cannot say that `beforeReceive` is somewhere their program can be has not
made a claim about their program.

An earlier version of this file concluded `¬ measure.AtFrontier beforeReceive`,
from a `frontierIsExternal` with no rank disjunct. That was true and vacuous:
local adversarial review proved the same argument applies to a *commit*, which
was then enabled at every network of every plan, so `AtFrontier` was empty for
every measure and every theorem in the progress module was about nothing.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.60 records what remains.

Quantified over every measure, which is the form that matters — this is not a
fact about one badly chosen measure but about the type.
-/
theorem pausing_beforeReceive_costs_rank {start : serverPlan.LogicalProcessNetwork}
    (measure : serverPlan.NetworkProgressMeasure start)
    (reached : measure.Reachable beforeReceive)
    (paused : measure.AtFrontier beforeReceive) :
    measure.rankLt (measure.rank afterReceive) (measure.rank beforeReceive) :=
  (measure.frontierIsExternal reached paused receiveAsStep).elim
    (fun entropy => absurd entropy the_receive_is_not_entropy) id

/-! ## What that costs a measure -/

/--
**The receive is a silent run of any measure that does not pause it.**

Half the non-vacuity: `no_infinite_silent_run` is about a class this plan can
put something in. What it cannot put in is an *infinite* sequence of them, which
is the theorem.

The `¬ AtFrontier` hypothesis was a theorem here until `frontierIsExternal`
gained its rank disjunct, and it was a theorem about an empty class — see
`pausing_beforeReceive_costs_rank`.
-/
theorem the_receive_is_a_silent_run {start : serverPlan.LogicalProcessNetwork}
    (measure : serverPlan.NetworkProgressMeasure start)
    (reached : measure.Reachable beforeReceive)
    (running : ¬ measure.AtFrontier beforeReceive) :
    ProcessPlan.NetworkProgressMeasure.SilentRun measure beforeReceive afterReceive :=
  .one receiveAsStep reached
    (fun emitted observation appended _ present => by
      rw [the_receive_emits_nothing emitted appended] at present
      exact absurd present (by simp))
    running

/--
**And every measure pays for it either way.**

The theorem the two branches converge on, and the one that does not depend on
whether a measure pauses this network. Paused, `pausing_beforeReceive_costs_rank`
charges the rank because a receive is not entropy. Not paused,
`descendsOrProduces` has two of its three disjuncts closed — the receive produces
nothing — so the rank descends. There is no hypothesis left for a measure to
wriggle out through.
-/
theorem every_measure_pays_for_the_receive {start : serverPlan.LogicalProcessNetwork}
    (measure : serverPlan.NetworkProgressMeasure start)
    (reached : measure.Reachable beforeReceive) :
    measure.rankLt (measure.rank afterReceive) (measure.rank beforeReceive) := by
  by_cases paused : measure.AtFrontier beforeReceive
  · exact pausing_beforeReceive_costs_rank measure reached paused
  · exact measure.silent_run_descends (the_receive_is_a_silent_run measure reached paused)

end Grass.Process.Tests.Progress
