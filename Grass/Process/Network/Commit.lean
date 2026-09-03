import Grass.Process.Network.Transition

/-!
# Commit and the desired view

`docs/PROCESS.md` §6 is short, and one sentence in it carries the whole module:

> A platform reconciler proves that each physical commit refines that view under
> an observation filter. It may skip an intermediate render or replace several
> pending renders by the latest one only when no skipped render has a demanded
> commit observation.

Everything else in §6 is a list of what a commit transition is indexed by, and
most of those indices belong to layers this one cannot see — physical worlds and
affected resource identities are the memory owner's, obligations are too. What
is here is the part that is a *process* fact: which pending renders a reconciler
may drop, and the proof that dropping them loses no demanded observation.

## Coalescing is the operation, and the side condition is the point

A reconciler that could coalesce freely would be a reconciler that could drop
any observation a specification demanded — the graphics case in §6, where
several frames are pending and only the latest is presented. A reconciler that
could never coalesce would have to present every intermediate frame, which is
the fiction §6 exists to remove.

`skippedUndemanded` is the side condition, and it is stated the way
`Grass/Process/Network/Escrow.lean` states its consumption law: as a property of
the *skipped* list rather than of the survivor, because "no skipped render has a
demanded commit observation" is a claim about what was dropped and not about
what remains.

## What `Demanded` is, and what it is not

An observation filter, supplied. `docs/PROCESS.md` §6 says a reconciler proves
refinement "under an observation filter", and the filter is the specification's
— which is `Grass.Semantics`'s, not this layer's. So it is a parameter, exactly
as `Grass/Process/Network/World.lean` parameterizes the obligation ledger and
for the same reason: reaching into another layer to state a process fact is the
import edge `coord1:5`'s diamond exists to prevent.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

/--
A pending render: something the process wants shown, not yet committed.

`docs/PROCESS.md` §6's "desired logical view", at the granularity a reconciler
works on. The observations are what committing it would append.
-/
structure PendingRender (Observation : Type u) where
  /-- What committing this render would append to the trace. -/
  observations : Trace Observation

namespace PendingRender

variable {Observation : Type u}

/--
A render whose observations the specification demands.

The filter is supplied; see the module note on why this layer cannot own it.
-/
def Demanded (demanded : Observation → Prop) (render : PendingRender Observation) : Prop :=
  ∃ observation ∈ render.observations, demanded observation

/-- A render that appends nothing is demanded by no filter. -/
theorem empty_not_demanded (demanded : Observation → Prop)
    (render : PendingRender Observation) (nothing : render.observations = []) :
    ¬ render.Demanded demanded := by
  rintro ⟨_, present, _⟩
  rw [nothing] at present
  exact absurd present List.not_mem_nil

end PendingRender

/--
**A reconciler's coalescing decision.**

`docs/PROCESS.md` §6: a reconciler "may skip an intermediate render or replace
several pending renders by the latest one only when no skipped render has a
demanded commit observation".

`exact` is the split, as one equation rather than three side conditions, so
nothing can be added or lost between the pending list and the pair of lists that
account for it — the same shape `Grass/Process/Network/Mailbox.lean` uses for
selective receive, and for the same reason.

`pending` is a field rather than a parameter. That is not a style choice: as a
parameter it appears in the structure's own type, so a theorem concluding
`committed ∈ pending` cannot be proved by rewriting with `exact` — the motive
would have to change the type of the `Coalescing` being reasoned about. As a
field the equation rewrites cleanly, and the conservation theorems below are
one line each instead of impossible.
-/
structure Coalescing {Observation : Type u} (demanded : Observation → Prop) where
  /-- The renders awaiting reconciliation, oldest first. -/
  pending : List (PendingRender Observation)
  /-- The renders skipped, in order. -/
  skipped : List (PendingRender Observation)
  /-- The one committed. -/
  committed : PendingRender Observation
  /-- Everything after it, still pending. -/
  rest : List (PendingRender Observation)
  /-- The pending list is exactly the skipped prefix, the survivor, and the rest. -/
  exact : pending = skipped ++ committed :: rest
  /--
  **And nothing skipped had a demanded observation.**

  §6's side condition, and the only thing standing between a reconciler and
  dropping an observation a specification required.
  -/
  skippedUndemanded : ∀ render ∈ skipped, ¬ render.Demanded demanded

namespace Coalescing

variable {Observation : Type u} {demanded : Observation → Prop}

/--
**No demanded observation is lost.**

The theorem §6's side condition exists to support: an observation the
specification demanded, on a render that was skipped, is impossible. Not "is
recovered later" — impossible, because such a render could not have been
skipped.
-/
theorem no_demanded_observation_dropped (coalescing : Coalescing demanded)
    {render : PendingRender Observation} (skipped : render ∈ coalescing.skipped)
    {observation : Observation} (present : observation ∈ render.observations)
    (isDemanded : demanded observation) : False :=
  coalescing.skippedUndemanded render skipped ⟨observation, present, isDemanded⟩

/-- The committed render was one of the pending ones. -/
theorem committed_was_pending (coalescing : Coalescing demanded) :
    coalescing.committed ∈ coalescing.pending := by
  rw [coalescing.exact]
  exact List.mem_append_right _ List.mem_cons_self

/-- And so was everything skipped. -/
theorem skipped_were_pending (coalescing : Coalescing demanded)
    {render : PendingRender Observation} (skipped : render ∈ coalescing.skipped) :
    render ∈ coalescing.pending := by
  rw [coalescing.exact]
  exact List.mem_append_left _ skipped

/--
Nothing was invented: every render in the split was pending.

With `exact` this is the conservation half — the reconciler accounts for the
pending list rather than replacing it with a list of its own.
-/
theorem accounted (coalescing : Coalescing demanded)
    {render : PendingRender Observation}
    (inSplit : render ∈ coalescing.skipped ∨ render = coalescing.committed ∨
      render ∈ coalescing.rest) : render ∈ coalescing.pending := by
  rw [coalescing.exact]
  rcases inSplit with wasSkipped | isCommitted | inRest
  · exact List.mem_append_left _ wasSkipped
  · exact List.mem_append_right _ (isCommitted ▸ List.mem_cons_self)
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ inRest)

/--
**A reconciler that skips nothing is always available.**

So the side condition never makes reconciliation impossible: presenting every
render in order is a `Coalescing`, whatever the filter demands. That matters
because a law that could not be satisfied would be a law forbidding commits, not
a law about which ones may be skipped.
-/
def skipNothing (demanded : Observation → Prop) (first : PendingRender Observation)
    (rest : List (PendingRender Observation)) : Coalescing demanded where
  pending := first :: rest
  skipped := []
  committed := first
  rest := rest
  exact := rfl
  skippedUndemanded := by
    intro render present
    exact absurd present List.not_mem_nil

end Coalescing

namespace ProcessPlan

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o}
  (plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations)

/--
A commit appends exactly the committed render's observations.

`docs/PROCESS.md` §6's commit transition, at the one index this layer owns:
"observations appended by the commit". The other indices §6 lists — physical
pre/post worlds, affected resource identities, obligations created and
discharged — belong to layers `Grass.Process` cannot see, and are not silently
omitted here so much as owed by whoever composes this with them.

The transition itself is `Grass/Process/Network/Transition.lean`'s `commit`
constructor, whose scope is the two observation fragments; this is the law
relating what it appends to what the reconciler chose.
-/
structure CommitsRender (before after : plan.LogicalProcessNetwork)
    {demanded : boundary.Observation → Prop}
    (coalescing : Coalescing demanded) : Prop where
  /-- The trace grew by exactly the committed render's observations. -/
  appended : after.observations = before.observations ++ coalescing.committed.observations
  /--
  **And what it published was pending, and only that leaves the pending trace.**

  `Commits.earned`, as a field of this structure rather than a hypothesis of
  `toCommits`. It was a hypothesis for one round, on the reasoning that
  `CommitsRender` is about a reconciler's split of pending *renders* while
  `Commits.earned` is about the world's pending *observation* trace, so this
  module could not supply the equation.

  That is the argument a field refutes: a field is a *demand on the constructor*,
  not something the module supplies. A reviewer read the signature — the same
  tell as §10.106's `initial_is_wellformed` — and compiled the consequence: a
  `CommitsRender` that publishes the pending observation **and invents two more
  pending observations nothing emitted**, because `scope` names `.pending` and no
  field said how `.pending` moved.
  `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.108.
  -/
  earned : before.pending = coalescing.committed.observations ++ after.pending
  /--
  And nothing outside the two observation traces changed — nothing at all if the
  committed render was empty.

  The `≠ []` guard matches `Grass/Process/Network/Transition.lean`'s `Commits`:
  a commit that appends nothing has not touched either trace, and saying it did
  would make it non-independent of every other emitting step for no reason.

  `.pending` is here because a commit *consumes* what it publishes. Until that
  fragment existed a commit only appended, which is what left it with no
  provenance at all — see `Commits.earned`.
  -/
  scope : plan.TouchesOnly before after
    (fun fragment =>
      coalescing.committed.observations ≠ [] ∧
        (fragment = .observations ∨ fragment = .pending))

namespace CommitsRender

variable {plan}

/--
A commit is a `Commits`, so it is a `NetworkTransition.commit` — provided the
render it committed carried something, and provided the caller can say which
live process produced it.

`rendered` is `Commits.nonempty`, and it is not a formality: a commit that
appends nothing changes nothing at all, which would make it a one-step silent
cycle and `Grass/Process/Network/Progress.lean`'s §7 theorem vacuous. A
reconciler that skipped every render has not committed; it has decided not to.

`earned` is `Commits`'s provenance field, and it is a *field* of this structure
since §10.108 — it was a hypothesis of this theorem for one round, and a reviewer
built the `CommitsRender` that hypothesis permitted.

The gap `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.58 records is still real and
is narrower than it was: the render ledger and the world's pending trace are two
accounts of the same thing, and `earned` now ties the *trace* to what was
published without tying it to the *renders* the reconciler split.
-/
theorem toCommits {before after demanded} {coalescing : Coalescing demanded}
    (commit : plan.CommitsRender before after coalescing)
    (rendered : coalescing.committed.observations ≠ []) :
    plan.Commits before after coalescing.committed.observations :=
  { earned := commit.earned, appended := commit.appended,
    nonempty := rendered, scope := commit.scope }

/--
**A commit drops no demanded observation.**

The whole point, assembled: the reconciler's split accounts for every pending
render, the skipped ones had no demanded observation, and the trace grew by
exactly what the survivor carried.
-/
theorem no_demanded_observation_dropped {before after demanded}
    {coalescing : Coalescing demanded}
    (_commit : plan.CommitsRender before after coalescing)
    {render : PendingRender boundary.Observation}
    (skipped : render ∈ coalescing.skipped)
    {observation : boundary.Observation} (present : observation ∈ render.observations)
    (isDemanded : demanded observation) : False :=
  coalescing.no_demanded_observation_dropped skipped present isDemanded

/-- And it appends, rather than rewriting: what was observed stays observed. -/
theorem earlier_observations_survive {before after demanded}
    {coalescing : Coalescing demanded}
    (commit : plan.CommitsRender before after coalescing)
    {observation : boundary.Observation}
    (wasObserved : observation ∈ before.observations) :
    observation ∈ after.observations := by
  rw [commit.appended]
  exact List.mem_append_left _ wasObserved

end CommitsRender

end ProcessPlan

end Grass.Process
