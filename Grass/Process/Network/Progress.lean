import Grass.Process.Network.Initial

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

## The shape of the argument

§7's sentence is about infinite runs, and `no_infinite_silent_run` is that
literally: there is no sequence of networks each of which reaches the next by
silent, off-frontier steps. It needs no coinduction and no stream type — a
`Nat`-indexed family and `no_infinite_descent`, which is `WellFounded.apply`
followed by induction on accessibility.

**A first draft got this wrong in a way worth recording**, because the wrong
version looked complete. It proved only `no_silent_cycle` — no silent run
returns to where it started — and argued that an infinite run in a finite state
space is a cycle while an infinite run in an infinite one "descends forever,
which the rank forbids directly". The second half was prose; nothing stated it.
And the first half applies to no plan in this corpus, because the network state
space is **append-only on every axis**: `NominalHistory.extend`,
`LedgerExtends.createdPrefix`, `Commits.appended`, `Delivers.cursorAdvances`.

Local adversarial review then made that sharp, and the result is the reason the
cycle law had to be replaced rather than supplemented. Both livelocks §7 names
by hand are provably *not* cycles:

* a fresh-child restart loop allocates a nominal on every restart, and
  `NetworkStep.allocations_were_fresh` plus `historyExact` make a cycle through
  an allocation contradictory — so a restart loop is an infinite *non-repeating*
  run, exactly what a cycle law cannot see;
* a send-then-receive loop advances the receiver's cursor by one
  (`Delivers.cursorAdvances`) and the send does not move it back.

So the module's headline theorem excluded neither of the two cases it advertised.
`no_silent_cycle` survives as a corollary and is stated as one.

## What "silent" excludes, and what it does not

`SilentRun` requires of each step that it added no specification-demanded
observation and did not start at a declared frontier. It says nothing about
which *constructor* the step was, and that is deliberate — §7's list ("process
steps, spawn, retry, cancellation, death, join, and restart") is the whole
family, so a law that enumerated constructors would be a law that a new
constructor could evade.

A self-delivered livelock and a fresh-child restart loop are both infinite
silent runs, and `no_infinite_silent_run` excludes them as such — not because
they repeat a state, which they provably do not, but because each of their steps
would have to descend a well-founded rank.

That is where §7's "local progress is necessary but insufficient" bites: both
processes in a self-delivery loop may have perfectly good local ranks, each
answering the messages it is sent, while the network as a whole makes no
progress the specification can see.

## What is supplied and what is derived

`NetworkProgressMeasure` is supplied by whoever proves a plan adequate, and is
indexed by the network a run of it begins at. Its one field with content is
`descendsOrProduces`, and it is deliberately a *disjunction* rather than an
unconditional descent: §7 permits a step to make no progress on the rank provided
it produced a demanded observation or was the outside acting, and a measure that
forbade those would be unsatisfiable for any long-lived process.

Both are also quantified over the measure's own `Reachable`, and that index is
why any plan that does interesting work can have a measure at all. The world is a
record type, so most of its inhabitants are worlds no execution produces, and a
measure quantified over all of them has to pay for a spawn/die/restart chain
among worlds no run reaches. `Tests/Process/FrontierFixtures.lean` is the plan
small enough to afford that, and it is the only one.

`Reachable` is not free: `reachableStart` and `reachableClosed` force it to
contain everything an execution from `start` can reach, so the least choice is
exactly `plan.StepsTo start`. And `startIsInitial` requires `start` to be a
network a run may begin at — `Grass/Process/Network/Initial.lean`'s
`ExactInitialNetwork`, which `Tests/Process/FrontierFixtures.lean` inhabits.

`rankTransitive` is a field because well-foundedness does not imply transitivity
and the cycle argument needs it. `rank_is_irreflexive` is derived, not assumed.

## What a measure still owes, and one thing this found

A measure can no longer declare anything paused, and three rounds went into
learning that it should not be able to. `AtFrontier` was a field with an
obligation attached; the obligation was either unsatisfiable, which made the
predicate empty for every measure, or satisfiable by declaring *everything*
paused, which emptied the `SilentRun` class instead. Both versions made this
module's theorems vacuous at the corpus's only plan, and a reviewer built the
witness each time.

The predicate is now a definition about which steps are enabled, and the
per-step question — *was this step the outside acting?* — is a disjunct of
`descendsOrProduces`. `Grass/Process/Progress.lean` separates waiting from
spinning with `ProcessEvent.externalEntropy` and has never had a frontier
predicate; the two layers now agree.

`Tests/Process/FrontierFixtures.lean` is worth reading beside this: its
`entropy_or_descends` is the twenty-four-case analysis a measure at that plan
needs, and `the_plan_is_useful` and `waiting_is_at_a_frontier` are now theorems
about the plan rather than claims a measure makes.

Trying to build a measure at the M2 fixture plan is what found two no-op
transitions, each of which would have forced every measure to declare a network
at a frontier for no reason: `commit []`, closed by `Commits.nonempty`, and
`requestCancel` against an already-requested occurrence, closed by
`RequestsCancel.wasNotRequested`. Neither was caught by
`self_independent_iff_scopeless`, because both had non-empty scopes.

**What is still owed**, and is not addressed here at all: §7's conditional
responsiveness and its coherent strategy; "reach a law-bearing external/
demand-result frontier *in finite internal work*", of which `AtFrontier` carries
neither the finiteness nor the law-bearing content; long-lived processes'
productivity, reactivity and conditional quiescence; supervision's restart bound
or separately demanded productivity law; scheduler fairness being used only when
named; and any network analogue of `Grass/Process/Progress.lean`'s enabledness
theorems, without which "maximal execution" has no referent here.

`demanded` and `AtFrontier` are also free predicates chosen by the same author
who supplies the rank, where §7's obligation is indexed by the `spec`. The
per-process analogue derives demandedness from `ProcessAcceptance`; this one
cannot, because a `ProcessPlan` does not hold the specification.
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
    Obligations) (start : plan.LogicalProcessNetwork) where
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
  /--
  **Which networks a run of this plan can be at.**

  `LogicalProcessNetwork` is a record type, so most of its inhabitants are worlds
  no execution produces: an empty instance slot, a dead incarnation with no
  history, an instance attached to a parent that was never spawned. The two
  obligations below used to be quantified over all of them, and a measure had to
  pay for a step from each — which is why no plan that does anything had one.
  `serverPlan`'s unreachable worlds admit an unbounded spawn/die/restart chain
  with no external event, so no rank descends across it, whatever its reachable
  executions do.

  This is the same repair `MeetsProcessProgress` was given one layer down for the
  same reason, and it is not a free predicate. `reachableStart` and
  `reachableClosed` force it to contain everything an execution from `start` can
  reach, so the *least* choice is exactly `plan.StepsTo start` and every other is
  wider. In particular `fun _ => False` is not available, which is the escape
  hatch a freely-chosen predicate would have opened.

`startIsInitial` below ties `start` to a network a run may actually begin at.
  -/
  Reachable : plan.LogicalProcessNetwork → Prop
  /--
  **And the start is a network a run may begin at.**

  Without this a measure could be indexed by a world no execution produces —
  an empty network, or one whose root carries a generation nothing allocated —
  and discharge `reachableStart` vacuously, which puts the whole reachability
  index back where it came from.

  It could not be stated until `Grass/Process/Network/Initial.lean`'s
  `ExactInitialNetwork` had a witness, because a field demanding an uninhabited
  record makes *this* record uninhabited too.
  `Tests/Process/FrontierFixtures.lean`'s `waiting_is_a_start` is that witness
  and `waitingMeasure` is the measure it unblocked.

  The request is existentially quantified, and that costs nothing: a network is
  a start for at most one request, because `onlyTheRoot` forces one live slot,
  `rootPresent` forces one incarnation in it, and `rootRequest` reads the request
  off that incarnation. An earlier version of this docstring called the
  quantification a choice needing a ruling, and a reviewer proved it is
  determined — `ExactInitialNetwork.request_is_determined` is the theorem.
  -/
  startIsInitial : ∃ request, Nonempty (plan.ExactInitialNetwork request start)
  /-- The start is reachable. -/
  reachableStart : Reachable start
  /-- And a step from a reachable network reaches a reachable one. -/
  reachableClosed : ∀ {before after : plan.LogicalProcessNetwork},
    Reachable before → plan.NetworkStep before after → Reachable after
  /--
  **§7's disjunction: every reachable step descends, produces, or was the
  outside acting.**

  A disjunction rather than an unconditional descent, because §7 permits a step
  to make no progress on the rank provided it "produced an independently
  specified observation" or "reached a law-bearing external/demand-result
  frontier" — and a long-lived process that never terminates has no
  unconditional descent to offer.

  **The entropy disjunct is §7's frontier clause, and getting it wrong cost two
  rounds.** The frontier was a declared *predicate on networks* with a field
  saying such a network is left only by entropy or by a descending step. Two
  reviewers took that apart. The first version, "left only by entropy", made the
  predicate empty for every measure — a commit or a spawn is enabled almost
  everywhere and neither is entropy — so §7's escape was unreachable and every
  theorem here was vacuous. Adding the rank disjunct made the predicate
  inhabitable and then admitted the opposite degeneracy: a measure could declare
  *every* network paused and discharge the field from a case analysis it needed
  anyway, so the whole class of `SilentRun`s was empty and the theorems were
  vacuous again. A third reviewer built that measure.

  The mistake both times was that a frontier is not a property a measure
  declares. "Only the outside can move this network" is a fact about which steps
  are *enabled*, so `AtFrontier` below is a definition rather than a field, and
  the disjunct that belongs here is per-step: **this step was the outside
  acting**. `Grass/Process/Progress.lean` reached the same shape one layer down
  for the same reason.

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
    Reachable before → (step : plan.NetworkStep before after) →
    step.transition.DrivenByEntropy ∨
      rankLt (rank after) (rank before) ∨
      (∃ emitted observation, after.observations = before.observations ++ emitted ∧
        demanded observation ∧ observation ∈ emitted)

/--
**A network only the outside can move.**

`docs/PROCESS.md` §7's "declared external frontier", and it is a *definition*
rather than a declaration. Two rounds of review were spent on it as a field of
the measure. As a field it was either empty for every measure — when it demanded
that only entropy leave a frontier, which a commit or a spawn refutes almost
everywhere — or satisfied by declaring every network paused, which emptied the
`SilentRun` class instead. Neither version was about waiting.

The fact "the outside must act" is about which steps are *enabled* at a network,
and nothing about it is the measure's to choose. So it is stated here, once,
about the plan; a measure has no `AtFrontier` field and cannot get it wrong.

It does not appear in `descendsOrProduces` either. §7's frontier clause is
per-step — "this step was the outside acting" — and a network at a frontier is
one where every step is.
-/
def AtFrontier (network : plan.LogicalProcessNetwork) : Prop :=
  ∀ {after : plan.LogicalProcessNetwork} (step : plan.NetworkStep network after),
    step.transition.DrivenByEntropy

/--
**A plan with a network the outside is not needed to move.**

Was a property of a *measure*, and is now a property of the plan — which is
where it belonged: whether some network of a program can be moved by the program
itself has nothing to do with anyone's choice of rank.

Worth keeping because it is what a reader wants to know about a plan before
reading a progress claim about it. A plan every one of whose networks is at a
frontier is a program that only ever waits, and §7's theorem is true of it for an
uninteresting reason.
-/
def Useful (plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations) : Prop :=
  ∃ network, ¬ plan.AtFrontier network

namespace NetworkProgressMeasure

variable {start : plan.LogicalProcessNetwork} (measure : plan.NetworkProgressMeasure start)

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
A non-empty execution, every step of which was the program acting on itself and
produced nothing the specification asked for.

"Silent" is now per-step and means two things: the step is not
`DrivenByEntropy`, so the outside did not have to act for it, and it added no
demanded observation. That is exactly the shape
`Grass/Process/Progress.lean`'s `SilentStep` has one layer down, and the two
agreeing is not a coincidence — the network reached it by removing a declared
frontier predicate that the per-process layer never had.

The earlier condition was "did not start at a network the measure calls paused",
and it made the class empty at the corpus's only measure, because that measure
called every network paused. A reviewer proved it.

`.one` is the base rather than a reflexive `.still`, so a `SilentRun` has at
least one step by construction — which is what makes `no_silent_cycle` a
statement about loops rather than a statement about doing nothing.
-/
inductive SilentRun {start : plan.LogicalProcessNetwork}
    (measure : plan.NetworkProgressMeasure start) :
    plan.LogicalProcessNetwork → plan.LogicalProcessNetwork → Prop
  /-- One step, from a network a run can be at, which produced nothing demanded
  and did not start paused. -/
  | one {before after : plan.LogicalProcessNetwork} (step : plan.NetworkStep before after)
      (reached : measure.Reachable before)
      (produced : ∀ emitted observation, after.observations = before.observations ++ emitted →
        measure.demanded observation → observation ∉ emitted)
      (internal : ¬ step.transition.DrivenByEntropy) : SilentRun measure before after
  /-- And one more of the same. -/
  | more {first middle last : plan.LogicalProcessNetwork}
      (earlier : SilentRun measure first middle) (step : plan.NetworkStep middle last)
      (reached : measure.Reachable middle)
      (produced : ∀ emitted observation, last.observations = middle.observations ++ emitted →
        measure.demanded observation → observation ∉ emitted)
      (internal : ¬ step.transition.DrivenByEntropy) : SilentRun measure first last

/--
**A well-founded relation has no infinite descending sequence.**

Core has `WellFounded.apply` and accessibility induction and not this, so it is
four lines here. It is what turns a rank into a statement about *infinite* runs
without a stream type or a coinductive execution: a `Nat`-indexed family is
enough.
-/
theorem no_infinite_descent {α : Type _} {rank : α → α → Prop} (wellFounded : WellFounded rank)
    (sequence : Nat → α) (descends : ∀ index, rank (sequence (index + 1)) (sequence index)) :
    False := by
  have never : ∀ value, Acc rank value → ∀ index, sequence index ≠ value := by
    intro value accessible
    induction accessible with
    | intro current _ ih =>
      intro index isCurrent
      exact ih (sequence (index + 1)) (isCurrent ▸ descends index) (index + 1) rfl
  exact never (sequence 0) (wellFounded.apply (sequence 0)) 0 rfl

/--
**Every silent, off-frontier step descends.**

The disjunction resolved: `descendsOrProduces` offers three ways out, and a
`SilentRun`'s own fields close two of them.
-/
theorem silent_step_descends {before after : plan.LogicalProcessNetwork}
    (step : plan.NetworkStep before after)
    (reached : measure.Reachable before)
    (produced : ∀ emitted observation, after.observations = before.observations ++ emitted →
      measure.demanded observation → observation ∉ emitted)
    (internal : ¬ step.transition.DrivenByEntropy) :
    measure.rankLt (measure.rank after) (measure.rank before) := by
  rcases measure.descendsOrProduces reached step with entropy | descends |
    ⟨emitted, observation, appended, isDemanded, inSegment⟩
  · exact absurd entropy internal
  · exact descends
  · exact absurd inSegment (produced emitted observation appended isDemanded)

/-- **And so does a whole silent run.** -/
theorem silent_run_descends {before after : plan.LogicalProcessNetwork}
    (run : SilentRun measure before after) :
    measure.rankLt (measure.rank after) (measure.rank before) := by
  induction run with
  | one step reached produced internal =>
    exact measure.silent_step_descends step reached produced internal
  | more _ step reached produced internal earlierDescends =>
    exact measure.rankTransitive _ _ _
      (measure.silent_step_descends step reached produced internal) earlierDescends

/--
**And no silent cycle**, which is the same rank argument at a run that returns.

A corollary rather than the headline, and it excludes less than it appears to:
the network state space is append-only on every axis, so a genuine cycle is
close to impossible already, and in particular neither of §7's two named
livelocks is one. See the module note — an earlier version of this module made
this its main theorem and advertised exactly the two cases it could not see.
-/
theorem no_silent_cycle {network : plan.LogicalProcessNetwork}
    (cycle : SilentRun measure network network) : False :=
  measure.rank_is_irreflexive (measure.rank network) (measure.silent_run_descends cycle)

/--
**There is no infinite silent run.**

`docs/PROCESS.md` §7's theorem, at the shape it is actually about: no sequence
of networks each of which reaches the next by silent, off-frontier steps. A
fresh-child restart loop and a self-delivered livelock are both of this shape,
and neither is a cycle — see the module note for why that distinction sank an
earlier version of this module.

The proof is `silent_run_descends` at each index and `no_infinite_descent`. No
coinduction, no stream, and no finiteness assumption about the state space —
which matters, because the network state space is append-only and therefore
infinite in every plan that can spawn or commit twice.
-/
theorem no_infinite_silent_run (run : Nat → plan.LogicalProcessNetwork)
    (silent : ∀ index, SilentRun measure (run index) (run (index + 1))) : False :=
  no_infinite_descent measure.rankWellFounded (fun index => measure.rank (run index))
    (fun index => measure.silent_run_descends (silent index))

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
    (outInternal : ¬ out.transition.DrivenByEntropy)
    (reached : measure.Reachable network)
    (backProduced : ∀ emitted observation,
      network.observations = middle.observations ++ emitted →
      measure.demanded observation → observation ∉ emitted)
    (backInternal : ¬ back.transition.DrivenByEntropy) : False :=
  measure.no_silent_cycle
    (.more (.one out reached outProduced outInternal) back
      (measure.reachableClosed reached out) backProduced backInternal)

/--
**And two silent runs cannot be composed into a cycle.**

Not a no-revisiting law: the caller must supply the run already split at the
network it returns to, and `SilentRun` has no inversion at an interior point —
only `.more` peels a step, and it peels the last one. So a run that revisits a
network in the middle cannot be brought to this theorem. It is
`no_silent_cycle` for a concatenation, and an earlier docstring claimed
otherwise.
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
