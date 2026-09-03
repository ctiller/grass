import Grass.Process.Weave.Mixin

/-!
# Weaving two components, and what disjoint namespaces decide for you

`docs/PROCESS.md` §8 opens with a condition rather than a construction:

> `weave` constructs or refines a non-precious `ProcessPlan` from process
> machines with disjoint nominal event, demand, result, and observation
> namespaces.

and then lists six things the weave proves, the first of which is "how events
are routed and whether irrelevant events stutter".

This module is the argument that **bullet 1** — "how events are routed and
whether irrelevant events stutter" — is a *consequence* of the condition rather
than an obligation a weave discharges. Both of its clauses, at the level of
names: with disjoint namespaces a woven demand belongs to exactly one component,
so where its result must go is settled before any result exists, and so is the
question of whether the other component has anything to answer with.

A first draft said "the first two of those six", counting bullet 1's two clauses
as two bullets. §8's actual bullet 2 — "realized-demand dependency/concurrency
compatibility" — is not addressed here at all.

## What a `VocabularyEmbedding` has to carry

The demand map has to be injective and the result map has to go *backwards* —
from the whole's result for an embedded demand to the part's result for the
original. That direction is not a convenience: `ProcessVocabulary.Result` is
dependent, so a forward map would have to produce a result for a demand it was
not given, which is `docs/PROCESS.md` §5's "attach one result to another
occurrence" one level up.

Injectivity is what makes routing a function rather than a relation. Without it
two of a component's own demands could embed to one woven demand and a single
result would answer both — the multiplicity failure
`Grass/Process/Bag.lean` forbids inside one component, reappearing at the seam.

**And `result` is a field no theorem here consumes.** Local adversarial review
deleted it and every theorem below still held, and built a legal weave whose
logger `result` fabricates a byte count for every `write` — `docs/PROCESS.md`
§5's "may not fabricate a result", unenforced at the seam. It is kept because a
weave must supply the renaming to be usable at all, and constraining it needs
the two components' *plans*, not their vocabularies. Recorded as
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.50.

## What is not here

The other four things §8's weave proves — shared-state synchronisation,
observation ordering, cancellation and obligation propagation, and progress
preservation — are about the *plans*, not about their vocabularies. Two have
modules: `Grass/Process/Weave/Lens.lean` proves noninteraction for disjoint
refinement scopes, and `Grass/Process/Network/Progress.lean` states what a
progress measure owes. Observation ordering across components, and cancellation
and obligation propagation, have neither.

§8's bullet 2, "realized-demand dependency/concurrency compatibility", is also
absent and is about the plans rather than the vocabularies.

## Two things this structure does not require

**Coverage.** Nothing makes the two components' images *exhaust* the woven
vocabulary, so a woven demand may belong to neither. Every theorem below takes
`FromLeft` as a hypothesis and is therefore silent about such a demand. §8's
bullet is "how events are routed", unrestricted, so a plan that wants every
woven name owned owes a surjectivity argument this structure does not collect.

**Broadcast.** `externalEventsDisjoint` forbids one entropy waking both
components — one clock tick delivered to a logger and a timer at once, which is
ordinary parallel composition. Whether §8's "disjoint nominal event namespaces"
means to exclude that is a question about the document; the choice is made here
and is worth a reader knowing it was made.

A first draft named those four as a structure of four `Prop` fields. That is the
opaque-promise shape this layer keeps rejecting — `True` four times discharges
it, and a weave carrying one would look more complete than a weave carrying
nothing. Left as prose for the same reason `Grass/Process/Weave/Lens.lean`
leaves its boundary-preservation note as prose.
-/

namespace Grass.Process

open Grass.Specification

universe u

/-! ## Embedding one component's vocabulary in a woven one -/

/--
One component's names, inside a woven vocabulary.

Every field is a renaming except `result`, which runs backwards; see the module
note for why it has to.
-/
structure VocabularyEmbedding (part whole : ProcessVocabulary.{u}) : Type u where
  /-- Where this component's entropy appears. -/
  externalEvent : part.ExternalEvent → whole.ExternalEvent
  /-- Where its demands appear. -/
  demand : part.Demand → whole.Demand
  /--
  **And no two of its demands land on one.**

  What makes `Routes` a function rather than a relation, and the seam-level form
  of the multiplicity law `Grass/Process/Bag.lean` enforces inside a component.
  -/
  demandInjective : ∀ left right, demand left = demand right → left = right
  /--
  An answer to the embedded demand is an answer to the original.

  Backwards, and dependently: the woven result type is indexed by the *embedded*
  demand, so this cannot be a renaming in the other direction without producing
  a result for a demand it was not handed.
  -/
  result : ∀ own, whole.Result (demand own) → part.Result own
  /-- And no two of its entropies land on one either. -/
  externalEventInjective : ∀ left right,
    externalEvent left = externalEvent right → left = right
  /-- Where its observations appear. -/
  observation : part.Observation → whole.Observation
  /-- And no two of its observations land on one. -/
  observationInjective : ∀ left right, observation left = observation right → left = right
  /--
  Where its interruption reasons, faults and environment violations appear.

  `ProcessVocabulary` has seven fields and a first draft of this structure mapped
  four. `Grass/Process/Network/Delivery.lean` records `agent-bus` disposition
  `g-design:4` — "cross-vocabulary delivery owes a total classifier; an empty
  target class proves unreachability" — and a weave is exactly such a boundary.

  Without these three, local adversarial review built a legal weave whose part
  had `LogicalFault := Bool` and whose whole had `Empty`: a component that can
  fail, woven into a program that has declared no fault can occur. Totality is
  what makes the empty target *prove* unreachability rather than hide it.
  -/
  interruptReason : part.InterruptReason → whole.InterruptReason
  /-- Its faults. -/
  logicalFault : part.LogicalFault → whole.LogicalFault
  /-- And its environment violations. -/
  environmentViolation : part.EnvironmentViolation → whole.EnvironmentViolation

/-! ## Two components, woven -/

/--
`docs/PROCESS.md` §8's disjointness condition, as a structure.

Only the demand and observation namespaces are required disjoint here, because
those are the two the theorems below use. §8 also names events and results:
events have `externalEventsDisjoint`. *Results* need no field of their own, and
the reason is about indices rather than types: two components' result *types*
collide freely — a logger's `write` and a timer's `sleep` may both answer with a
`Nat` — but `Result` is indexed by the demand, so a woven result is attached to
one demand and the demand namespaces are disjoint. A first draft said the types
could not collide, which is false.
-/
structure DisjointWeave (left right whole : ProcessVocabulary.{u}) : Type u where
  /-- The left component's names. -/
  leftIn : VocabularyEmbedding left whole
  /-- The right component's. -/
  rightIn : VocabularyEmbedding right whole
  /-- **No demand is both components'.** -/
  demandsDisjoint : ∀ own other, leftIn.demand own ≠ rightIn.demand other
  /-- **No observation is.** -/
  observationsDisjoint : ∀ own other, leftIn.observation own ≠ rightIn.observation other
  /-- **And no external event is.** -/
  externalEventsDisjoint : ∀ own other, leftIn.externalEvent own ≠ rightIn.externalEvent other

namespace DisjointWeave

variable {left right whole : ProcessVocabulary.{u}} (weave : DisjointWeave left right whole)

/-- A woven demand is the left component's. -/
def FromLeft (demand : whole.Demand) : Prop := ∃ own, weave.leftIn.demand own = demand

/-- Or the right's. -/
def FromRight (demand : whole.Demand) : Prop := ∃ own, weave.rightIn.demand own = demand

/--
**A woven demand is not both components'.**

§8's first bullet — "how events are routed" — at the demand side, and it is a
consequence of the disjointness rather than a routing table a weave supplies.
-/
theorem not_from_both {demand : whole.Demand}
    (fromLeft : weave.FromLeft demand) (fromRight : weave.FromRight demand) : False := by
  obtain ⟨own, isLeft⟩ := fromLeft
  obtain ⟨other, isRight⟩ := fromRight
  exact weave.demandsDisjoint own other (isLeft.trans isRight.symm)

/--
**And it comes from at most one demand of that component.**

Injectivity spent: the component's own demand is recovered, so a result for the
woven demand answers exactly one of its demands.
-/
theorem left_source_is_unique {demand : whole.Demand} {own other : left.Demand}
    (fromOwn : weave.leftIn.demand own = demand)
    (fromOther : weave.leftIn.demand other = demand) : own = other :=
  weave.leftIn.demandInjective own other (fromOwn.trans fromOther.symm)

/--
**A woven demand comes from exactly one demand of exactly one component.**

The vocabulary-level half of §8's routing bullet. It is about *names*, not about
a result and not about an execution — there is no `ProcessPlan` and no step
relation in this module, so "the result routes" is not expressible here. What is
expressible, and what a routing argument consumes, is that the destination is
determined before any result exists.

A first draft's docstring said "a result for a left demand routes to the left
component and nowhere else", and no result appears in the statement.
-/
theorem routing_is_forced {demand : whole.Demand} (fromLeft : weave.FromLeft demand) :
    (∃ own : left.Demand, weave.leftIn.demand own = demand ∧
        ∀ other, weave.leftIn.demand other = demand → other = own) ∧
      ¬ weave.FromRight demand := by
  obtain ⟨own, isOwn⟩ := fromLeft
  refine ⟨⟨own, isOwn, fun other isOther => weave.left_source_is_unique isOther isOwn⟩, ?_⟩
  exact fun fromRight => weave.not_from_both ⟨own, isOwn⟩ fromRight

/--
**And the other component has no demand that could have been meant.**

The vocabulary-level half of §8's "whether irrelevant events stutter". Stuttering
itself is a fact about executions and is not expressible here; what this says is
that the question has one answer before any execution is considered, which is
the part a weave would otherwise have to *choose*.

Equivalent to `demandsDisjoint` — local adversarial review derived the field back
from it — so it is a restatement in the form a consumer wants, not a new fact.
-/
theorem the_other_side_stutters {own : left.Demand} :
    ¬ ∃ other : right.Demand, weave.rightIn.demand other = weave.leftIn.demand own :=
  fun ⟨other, isRight⟩ => weave.demandsDisjoint own other isRight.symm

/-- The same at the observation namespace: an observation has one origin. -/
theorem observation_origin_is_unique {observed : whole.Observation}
    {own : left.Observation} {other : right.Observation}
    (fromLeft : weave.leftIn.observation own = observed)
    (fromRight : weave.rightIn.observation other = observed) : False :=
  weave.observationsDisjoint own other (fromLeft.trans fromRight.symm)

/-- And at the entropy namespace: an external event wakes one component. -/
theorem entropy_wakes_one_side {arrived : whole.ExternalEvent}
    {own : left.ExternalEvent} {other : right.ExternalEvent}
    (fromLeft : weave.leftIn.externalEvent own = arrived)
    (fromRight : weave.rightIn.externalEvent other = arrived) : False :=
  weave.externalEventsDisjoint own other (fromLeft.trans fromRight.symm)

end DisjointWeave


end Grass.Process
