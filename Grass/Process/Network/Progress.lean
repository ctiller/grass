import Grass.Process.Network.Transition

/-!
# Network progress: why a silent loop cannot run forever

`docs/PROCESS.md` §7 states the theorem this module proves:

> Local progress is necessary but insufficient. `ProcessNetworkAdequate` proves
> the corresponding theorem over every maximal network execution. An infinite
> network run must produce a specification-demanded observation or remain at a
> declared external frontier; otherwise a global well-founded rank decreases
> across process steps, spawn, retry, cancellation, death, join, and restart.
> Supervision therefore carries a restart bound/rank or a separately demanded
> productivity law. Fresh-child restart loops cannot evade the global theorem,
> and scheduler fairness is used only when named by the specification.

## The shape of the argument, and why it is a cycle law

"An infinite run must produce or pause" is a statement about infinite objects,
and this layer has no stream of networks — `NetworkStep` is a relation and an
execution is an inductive. What it *does* have is exactly what the disjunct's
`otherwise` clause names: a global well-founded rank that every silent,
off-frontier step decreases.

So the theorem here is the contrapositive at the shape a well-founded rank
actually forbids: **there is no non-empty silent, off-frontier execution that
returns to the network it started from** (`no_silent_cycle`). An infinite run in
a finite state space is a cycle; an infinite run in an infinite one descends
forever, which the rank forbids directly (`silent_run_descends`, plus
`WellFounded`). Both halves are here and neither needs a stream.

## What "silent" excludes, and what it does not

`SilentRun` requires of each step that it added no specification-demanded
observation and did not start at a declared frontier. It says nothing about
which *constructor* the step was, and that is deliberate — §7's list ("process
steps, spawn, retry, cancellation, death, join, and restart") is the whole
family, so a law that enumerated constructors would be a law that a new
constructor could evade.

`two_silent_steps_cannot_return` is the shape the exclusions §7 names actually
take. A self-delivered livelock — a process that sends to itself and receives,
forever — is two silent steps returning to where they started, and so is the
smallest fresh-child restart loop. Neither is a special case and neither needs a
lemma of its own, which is the point of not enumerating constructors.

That is also where §7's "local progress is necessary but insufficient" bites:
both processes in a self-delivery loop may have perfectly good local ranks,
each answering the messages it is sent, while the network revisits a state it
has already been in.

## What is supplied and what is derived

`NetworkProgressMeasure` is supplied by whoever proves a plan adequate. Its one
field with content is `descendsOrProduces`, and it is deliberately a
*disjunction* rather than an unconditional descent: §7 permits a step to make no
progress on the rank provided it produced a demanded observation or was sitting
at a frontier, and a measure that forbade those would be unsatisfiable for any
long-lived process.

`rankTransitive` is a field because well-foundedness does not imply transitivity
and the cycle argument needs it. `rank_is_irreflexive` is derived, not assumed.

## What a measure still owes, and one thing this found

`Useful` names the degeneracy that would make the whole theorem empty:
`AtFrontier := fun _ => True` discharges `descendsOrProduces` with no rank at
all. Supplying a *useful* measure for a real plan is the adequacy obligation
§7 assigns to `ProcessNetworkAdequate`, and it is not discharged anywhere yet.

Trying to build one at the M2 fixture plan is what found `Commits.nonempty`.
Without it `commit []` was a transition with an empty scope that changed
nothing — a one-step silent cycle at every network in every plan, which would
have forced every measure to declare everything at a frontier and made this
module's theorem vacuous everywhere.

An idle `processStep` — one whose protocol admits a self-transition on external
entropy — is *not* the same case and is not a defect: a process waiting on the
environment is at an external frontier, which is exactly the disjunct §7
provides for it.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

namespace ProcessPlan

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o} {plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations}

/--
A global measure for one plan, with §7's progress disjunction.

The whole content is `descendsOrProduces`. Everything else is the apparatus a
well-founded argument needs.
-/
structure NetworkProgressMeasure (plan : ProcessPlan.{u, w, v, r, m, o} registry boundary
    Obligations) where
  /-- The carrier of the global measure. -/
  Rank : Type u
  /-- Its strict order. -/
  rankLt : Rank → Rank → Prop
  /-- With no infinite descent. -/
  rankWellFounded : WellFounded rankLt
  /--
  And transitive.

  A field because well-foundedness does not give it, and the cycle argument
  needs to compose the descents of a whole execution into one.
  -/
  rankTransitive : ∀ a b c, rankLt a b → rankLt b c → rankLt a c
  /-- The measure. -/
  rank : plan.LogicalProcessNetwork → Rank
  /-- Which observations the specification demands. -/
  demanded : boundary.Observation → Prop
  /-- Which networks are sitting at a declared external frontier. -/
  AtFrontier : plan.LogicalProcessNetwork → Prop
  /--
  **§7's disjunction: every step descends, produces, or was paused.**

  A disjunction rather than an unconditional descent, because §7 permits a step
  to make no progress on the rank provided it produced a
  specification-demanded observation or was at a frontier — and a long-lived
  process that never terminates has no unconditional descent to offer.

  "Produced" is membership in the step's own *emitted segment*, not
  `observation ∈ after.observations ∧ observation ∉ before.observations`. The
  second form is multiplicity-blind, so a server that emits the same demanded
  observation on every request would satisfy it exactly once and never again —
  which is the class of defect
  `Grass/Process/Sequential/Adapter.lean` was rewritten to avoid at the pending
  bag. `Grass/Process/Trace/Linearization.lean`'s `observations_extend` supplies
  the segment for any step, so this costs a consumer nothing.
  -/
  descendsOrProduces : ∀ {before after : plan.LogicalProcessNetwork},
    plan.NetworkStep before after →
    rankLt (rank after) (rank before) ∨
      (∃ emitted observation, after.observations = before.observations ++ emitted ∧
        demanded observation ∧ observation ∈ emitted) ∨
      AtFrontier before

namespace NetworkProgressMeasure

variable (measure : plan.NetworkProgressMeasure)

/--
**A measure that pauses everything excludes nothing.**

`AtFrontier := fun _ => True` discharges `descendsOrProduces` with no rank at
all, and then no run is a `SilentRun` and `no_silent_cycle` is about an empty
class. Naming the non-degeneracy is the difference between a theorem and a
theorem shape.

`Useful` is deliberately weak — one running network is enough — because what
makes a measure *good* is a question about the plan, not about this structure.
`Tests/Process/ProgressFixtures.lean` exhibits the degenerate measure and shows
it fails this, so the reader can see which side of the line a measure is on.
-/
def Useful : Prop := ∃ network, ¬ measure.AtFrontier network

/--
A well-founded relation is irreflexive.

Derived rather than assumed, which matters: a measure that supplied
irreflexivity as a field could supply it of a relation that was not well founded
at all, and the cycle argument would then be about nothing.
-/
theorem rank_is_irreflexive (value : measure.Rank) : ¬ measure.rankLt value value := by
  induction value using measure.rankWellFounded.induction with
  | _ current ih =>
    intro self
    exact ih current self self

/--
A non-empty execution, every step of which was silent and off-frontier.

`.one` is the base rather than a reflexive `.still`, so a `SilentRun` has at
least one step by construction — which is what makes `no_silent_cycle` a
statement about loops rather than a statement about doing nothing.
-/
inductive SilentRun (measure : plan.NetworkProgressMeasure) :
    plan.LogicalProcessNetwork → plan.LogicalProcessNetwork → Prop
  /-- One step, which produced nothing demanded and did not start paused. -/
  | one {before after : plan.LogicalProcessNetwork} (step : plan.NetworkStep before after)
      (produced : ∀ emitted observation, after.observations = before.observations ++ emitted →
        measure.demanded observation → observation ∉ emitted)
      (running : ¬ measure.AtFrontier before) : SilentRun measure before after
  /-- And one more of the same. -/
  | more {first middle last : plan.LogicalProcessNetwork}
      (earlier : SilentRun measure first middle) (step : plan.NetworkStep middle last)
      (produced : ∀ emitted observation, last.observations = middle.observations ++ emitted →
        measure.demanded observation → observation ∉ emitted)
      (running : ¬ measure.AtFrontier middle) : SilentRun measure first last

/--
**Every silent, off-frontier step descends.**

The disjunction resolved: `descendsOrProduces` offers three ways out, and a
`SilentRun`'s own fields close two of them.
-/
theorem silent_step_descends {before after : plan.LogicalProcessNetwork}
    (step : plan.NetworkStep before after)
    (produced : ∀ emitted observation, after.observations = before.observations ++ emitted →
      measure.demanded observation → observation ∉ emitted)
    (running : ¬ measure.AtFrontier before) :
    measure.rankLt (measure.rank after) (measure.rank before) := by
  rcases measure.descendsOrProduces step with descends | ⟨emitted, observation, appended,
    isDemanded, inSegment⟩ | paused
  · exact descends
  · exact absurd inSegment (produced emitted observation appended isDemanded)
  · exact absurd paused running

/-- **And so does a whole silent run.** -/
theorem silent_run_descends {before after : plan.LogicalProcessNetwork}
    (run : SilentRun measure before after) :
    measure.rankLt (measure.rank after) (measure.rank before) := by
  induction run with
  | one step produced running => exact measure.silent_step_descends step produced running
  | more _ step produced running earlierDescends =>
    exact measure.rankTransitive _ _ _
      (measure.silent_step_descends step produced running) earlierDescends

/--
**So there is no silent cycle.**

`docs/PROCESS.md` §7's theorem at the shape a well-founded rank forbids: a
network cannot return to where it started by steps that produced no
specification-demanded observation and never paused at a frontier.

This is where §7's "local progress is necessary but insufficient" bites. Every
process in the loop may have a perfectly good local rank — each is answering the
messages it is sent — while the *network* revisits a state it has already been
in, forever.
-/
theorem no_silent_cycle {network : plan.LogicalProcessNetwork}
    (cycle : SilentRun measure network network) : False :=
  measure.rank_is_irreflexive (measure.rank network) (measure.silent_run_descends cycle)

/--
**Two silent steps cannot return to where they started.**

The shape a self-delivered livelock takes: a process sends to itself, receives,
and is back where it began. `docs/PROCESS_IMPLEMENTATION_PLAN.md`'s M4 exit
criterion names that case, and it needs no lemma of its own — which is the point
of `SilentRun` not enumerating constructors. The smallest fresh-child restart
loop, §7's other named evasion, is the same two steps.
-/
theorem two_silent_steps_cannot_return {network middle : plan.LogicalProcessNetwork}
    (out : plan.NetworkStep network middle) (back : plan.NetworkStep middle network)
    (outProduced : ∀ emitted observation,
      middle.observations = network.observations ++ emitted →
      measure.demanded observation → observation ∉ emitted)
    (outRunning : ¬ measure.AtFrontier network)
    (backProduced : ∀ emitted observation,
      network.observations = middle.observations ++ emitted →
      measure.demanded observation → observation ∉ emitted)
    (backRunning : ¬ measure.AtFrontier middle) : False :=
  measure.no_silent_cycle
    (.more (.one out outProduced outRunning) back backProduced backRunning)

/--
**And no silent run visits a network twice**, which is the same fact stated the
way an execution consumes it.
-/
theorem silent_run_does_not_repeat {first middle last : plan.LogicalProcessNetwork}
    (before : SilentRun measure first middle) (after : SilentRun measure middle last)
    (returned : first = last) : False := by
  subst returned
  exact measure.rank_is_irreflexive _
    (measure.rankTransitive _ _ _ (measure.silent_run_descends after)
      (measure.silent_run_descends before))

end NetworkProgressMeasure

end ProcessPlan

end Grass.Process
