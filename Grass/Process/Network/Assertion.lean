import Grass.Process.Network.Topology

/-!
# Network assertions

`docs/PROCESS.md` §3, on the channel contracts this module exists to support:

> Here `*` is separating conjunction over the logical process network, not
> physical heap separation. … Send and receive can therefore be checked locally
> while their composition is a library theorem.

`docs/PROCESS_IMPLEMENTATION_PLAN.md` standing risk 1 names the danger:

> If the assertion language grows toward a general separation logic it will eat
> this plan. The mitigation is that it is defined only over the named network
> fragments and has no frame rule beyond the one `WeaveInvariantMixin` needs.

So this module is deliberately small, and it is worth saying what it does *not*
contain: no points-to, no magic wand, no heap, no resource algebra of its own,
and no entailment relation. An assertion is a predicate over worlds, the set of
named fragments it may depend on, and a proof that it depends on nothing else.

## What separation means here

Not disjointness of memory — that is `docs/MEMORY_MODEL.md`'s, reached only
through the representation relation. Here it is disjointness of *named
fragments* of the logical network: this instance, that shared region, this
channel's escrow, that channel's session cursor, the obligation ledger, the
observation trace, the nominal history. Two assertions are separate when the
fragments they may read do not overlap.

That is weaker than a separation logic and it is what the channel contracts
need. A send's postcondition mentions the sender's local state and the escrow it
created; a receiver's precondition mentions the receiver's own session cursor.
Their composition is sound because those fragments are disjoint, and
`frame_of_disjoint_scope` below is the theorem that turns that into
preservation.

## `agreesGlue` is what makes a footprint a bound

`framed` alone does not make `footprint` mean anything, and an earlier revision
of this module claimed it did. The counterexample is one line: supply
`Agrees _ left right := (left = right)`, which is a perfectly legal equivalence
relation per fragment, and `framed` is discharged by `subst` for *any* predicate
at *any* footprint. Nothing became unsound — `frame`'s hypothesis is at the same
agreement, so it degenerated to `before = after` — but every framing obligation
in the weave became dischargeable only at identical worlds, and no theorem
noticed.

`agreesGlue` is the law that excludes it. It says any two worlds can be mixed
along any set of fragments, which is exactly the statement that the fragments
name a *complete and independent decomposition* of the world: agreement on a set
of fragments carries no information about the rest. Under the equality agreement
gluing at a proper subset would force `left = right`, so the degenerate
agreement is no longer a `WorldAgreement`.

It is a real obligation on whoever supplies the world, and the shape it demands
is a product over fragments. `docs/PROCESS.md` §3's `LogicalProcessNetwork` is
one — seven independent fields, with `instances`, `shared` and the two ledgers
pointwise over their indices — so the law is satisfiable there. A later world
that carried a cross-fragment well-formedness invariant *as a field* would not
satisfy it, and that is the right outcome: such a world's fragments would not be
independent, and its assertions could not be framed fragment-wise.

## The world is abstract on purpose

`LogicalProcessNetwork` is `Grass/Process/Network/Plan.lean`'s, and a plan needs
channel contracts, which need assertions. Rather than break that cycle by
guessing at the world's shape, this module takes an *agreement relation*: what
it means for two worlds to agree on one fragment. That is all a framing law
needs, and it lets the plan supply the real world later without this module
having invented a value universe to describe it.

`docs/PROCESS.md` §3 spells the type `NetworkAssertion topology`, with no world.
That arity is not implementable as the corpus stands, for reasons recorded in
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.11; this module's extra parameters are
the recorded divergence, not a silent one.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r x

/--
A named part of the logical network that an assertion may read.

These are the seven fields of `docs/PROCESS.md` §3's `LogicalProcessNetwork`,
with the three index-carrying ones refined to a single index: one instance
rather than the whole instance map, one region rather than all shared state, one
session's escrow rather than the whole ledger. The list is closed: an assertion
cannot depend on something with no name here, which is what keeps the language
from growing.

`escrow` and `session` are separate constructors because the world separates
them — `inFlight : ChannelEscrowLedger` and `sessions : ChannelSessionLedger` are
two fields — and because `docs/PROCESS.md` §3 requires
`ReceiverPre message occurrence * Escrow message occurrence` to be *formable*. A
single `channel` constructor covering both would put the receiver's cursor and
the escrowed payload in one fragment, `ReceiverPre` and `Escrow` would overlap,
and the one expression `Grass/Process/Network/Channel.lean` has to write would be
rejected.

`nominals` is here for the same kind of reason. §3 says freshness "means absence
from that monotone history", and `Escrow` owns "the unique affine
`ResolveToken occurrence.id`", so an assertion about at-most-one resolution
depends on `usedNominals`. Without a fragment naming it, such an assertion is
either unstatable or smuggled in through some other fragment's agreement.

`instanceState` names a *slot* — a `ProcessKind` and an `InstanceId` — and not a
`ProcessRef`. The world holds `instances : (kind) → InstanceId kind → Option
(ProcessInstance topology)`, one live incarnation per slot, with the generation
inside the stored instance rather than in the key. Keying the fragment by
`ProcessRef` instead would put two refs that differ only in generation on two
fragments reading one slot, and `agreesGlue` would then be unsatisfiable at the
real world: no mixed network can agree with one and not the other about the same
field. The cost is that framing over a slot is conservative — a restart replaces
the incarnation, touches the slot, and any assertion naming it must be
re-established — which is the correct reading of `docs/FOUNDATION.md` law 22
anyway, since a stale reference is meant to fail its generation check rather
than quietly frame past a replacement.
-/
inductive NetworkFragment {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary) : Type r
  /-- One instance slot's contents: the incarnation living there, if any, and
  its private state. -/
  | instanceState (kind : topology.ProcessKind) (slot : topology.InstanceId kind)
  /-- One named region of shared logical state. -/
  | region (region : topology.SharedRegion)
  /-- One channel session's in-flight escrow. -/
  | escrow (edge : topology.ChannelKind) (session : topology.ChannelId edge)
  /-- One channel session's endpoint cursors. -/
  | session (edge : topology.ChannelKind) (session : topology.ChannelId edge)
  /-- The obligation ledger. -/
  | obligations
  /-- The committed observation trace. -/
  | observations
  /--
  Observations processes have produced and the driver has not committed.

  `docs/PROCESS.md` §6 draws a line this world did not: "step emissions name only
  portable logical observations", and "a driver commit is the sole transition
  allowed to change provider resources or **append a committed external
  observation**". With one trace, `processStep` and `commit` both appended to it,
  the commit had nothing to be about, and `Commits` constrained the trace and
  nothing else — so a commit of an arbitrary observation was a legal step of
  *every* network. Local adversarial review proved that generically and drew the
  consequence: `.commit` is not `DrivenByEntropy`, so
  `NetworkProgressMeasure.frontierIsExternal` then forbids *any* network from
  being at a frontier, and §7's whole progress module is vacuous.

  With two fragments, a step produces into `pending` and a commit moves a prefix
  of `pending` into `observations`. A commit can only publish what a process
  actually emitted, and it can publish it once.
  -/
  | pending
  /-- The monotone nominal history that freshness is absence from. -/
  | nominals

/--
What it means for two worlds to agree on one fragment.

An interface rather than a definition, because the world is
`Grass/Process/Network/Plan.lean`'s and a plan needs the channel contracts this
module supports.

The first three laws are what a framing argument uses. `agreesGlue` is what
makes framing *say* anything; see the module note.
-/
structure WorldAgreement {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary)
    (World : Type x) where
  /-- These two worlds are indistinguishable on this fragment. -/
  Agrees : NetworkFragment topology → World → World → Prop
  /-- A world agrees with itself. -/
  agreesRefl : ∀ fragment world, Agrees fragment world world
  /-- Agreement is symmetric. -/
  agreesSymm : ∀ fragment left right,
    Agrees fragment left right → Agrees fragment right left
  /-- And transitive, so agreement composes along an execution. -/
  agreesTrans : ∀ fragment a b c,
    Agrees fragment a b → Agrees fragment b c → Agrees fragment a c
  /--
  **The fragments decompose the world.**

  Any two worlds can be mixed along any set of fragments. This is what excludes
  a degenerate agreement — equality, say — under which agreeing on a footprint
  would force agreement everywhere and `footprint` would carry no information.
  -/
  agreesGlue : ∀ (inside : NetworkFragment topology → Prop) (left right : World),
    ∃ mixed,
      (∀ fragment, inside fragment → Agrees fragment mixed left) ∧
      (∀ fragment, ¬ inside fragment → Agrees fragment mixed right)

namespace WorldAgreement

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
  {World : Type x}

/--
**Gluing kills the equality agreement.**

If agreement forced the worlds to be identical, then gluing at `obligations`
would produce a world that equals the first (because it agrees there) and equals
the second (because it agrees at `observations`, which is outside). So the world
would have at most one value, and there would be nothing to frame.

Stated here rather than left to the reader because it is the whole reason
`agreesGlue` is a field: an earlier revision of this module claimed `framed` was
"the whole content" of a `NetworkAssertion`, and the equality agreement was the
one-line refutation. This theorem is what makes the claim true instead.
-/
theorem subsingleton_of_forced_equality (agreement : WorldAgreement topology World)
    (forcesEqual : ∀ fragment left right,
      agreement.Agrees fragment left right → left = right)
    (left right : World) : left = right := by
  obtain ⟨mixed, insideAgrees, outsideAgrees⟩ :=
    agreement.agreesGlue
      (fun candidate => candidate = NetworkFragment.obligations) left right
  have toLeft : mixed = left :=
    forcesEqual _ _ _ (insideAgrees NetworkFragment.obligations rfl)
  have toRight : mixed = right :=
    forcesEqual _ _ _ (outsideAgrees NetworkFragment.observations (by simp))
  exact toLeft.symm.trans toRight

end WorldAgreement

/--
An assertion over the logical network: a predicate over worlds, the fragments it
may read, and a proof that it reads nothing else.

`footprint` is a *predicate* and not a list. `docs/PROCESS.md` §3's populations
are generative — "one request process per accepted connection up to a resource
policy" — so the footprints this module's own consumers need are not finite: a
`WeaveInvariantMixin` over every live connection's cursor, or a claim that no
other channel holds escrow for an occurrence, cannot be enumerated. A list would
have made those unstatable, and would have been discovered only once
`Grass/Process/Network/Channel.lean` was written against it.

`footprint` is an upper bound, not an exact read set. An assertion may name more
fragments than it reads, which is conservative for framing and means that
non-overlap of footprints implies nothing about what is actually read.
-/
structure NetworkAssertion {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
    {World : Type x} (agreement : WorldAgreement topology World) where
  /-- What it says. -/
  holds : World → Prop
  /-- The fragments it may read. -/
  footprint : NetworkFragment topology → Prop
  /-- And it reads nothing outside them. -/
  framed : ∀ left right,
    (∀ fragment, footprint fragment → agreement.Agrees fragment left right) →
    (holds left ↔ holds right)

namespace NetworkAssertion

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
  {World : Type x} {agreement : WorldAgreement topology World}

/--
The `Iff` in `framed` is redundant, and here is the proof.

Because `agreesSymm` is a field, a one-way `framed` gives the two-way one by
instantiating at the swapped worlds. Recorded rather than left implicit, because
otherwise no fixture could ever catch the `Iff` being weakened to an implication
— which makes it a claim about this type that only a theorem can carry.
-/
theorem framed_backward (assertion : NetworkAssertion agreement) (left right : World)
    (agrees : ∀ fragment, assertion.footprint fragment →
      agreement.Agrees fragment left right)
    (held : assertion.holds right) : assertion.holds left :=
  (assertion.framed right left
    (fun fragment member =>
      agreement.agreesSymm fragment left right (agrees fragment member))).mp held

/-- Two assertions are separate when the fragments they may read do not overlap. -/
def Separate (left right : NetworkAssertion agreement) : Prop :=
  ∀ fragment, left.footprint fragment → ¬ right.footprint fragment

theorem separate_symm {left right : NetworkAssertion agreement}
    (separate : Separate left right) : Separate right left :=
  fun fragment inRight inLeft => separate fragment inLeft inRight

/--
An assertion survives any change that leaves its fragments alone.

The raw form, in which the caller already holds agreement on the footprint.
`frame_of_disjoint_scope` below is the one `docs/PROCESS.md` §8 actually asks
for; this is the lemma it is built from.
-/
theorem frame (assertion : NetworkAssertion agreement) {before after : World}
    (untouched : ∀ fragment, assertion.footprint fragment →
      agreement.Agrees fragment before after)
    (held : assertion.holds before) : assertion.holds after :=
  (assertion.framed before after untouched).mp held

/--
**The frame rule, in the shape `WeaveInvariantMixin` needs.**

`docs/PROCESS.md` §8 declares the obligation as

> ```lean
> frame : forall (step : NetworkStep plan before after),
>   Disjoint (TransitionScope step) Scope ->
>   assertion before -> assertion after
> ```

— scope-versus-scope disjointness implies preservation. `frame` above does not
have that shape: it demands agreement on the footprint, which is the *conclusion*
of a framing argument rather than its premise. This is the step that closes the
gap. `scope` is the transition's scope, `disjoint` is §8's `Disjoint`, and
`touchesOnly` is what a `NetworkStep` supplies: a step changes nothing outside
its own scope.

One deviation is worth stating rather than leaving to be discovered. §8's field
is `Scope : NetworkScope plan`, a plan-level notion this layer does not have.
What stands in for it here is a fragment predicate — the same type as
`footprint` — which is the natural reading and is what `Plan.lean` will have to
supply `NetworkScope` as. If it turns out to be something else, this theorem is
where the mismatch surfaces.
-/
theorem frame_of_disjoint_scope (assertion : NetworkAssertion agreement)
    (scope : NetworkFragment topology → Prop)
    (disjoint : ∀ fragment, scope fragment → ¬ assertion.footprint fragment)
    {before after : World}
    (touchesOnly : ∀ fragment, ¬ scope fragment →
      agreement.Agrees fragment before after)
    (held : assertion.holds before) : assertion.holds after :=
  assertion.frame
    (fun fragment member => touchesOnly fragment
      (fun inScope => disjoint fragment inScope member)) held

/--
Separating conjunction: both hold, and they read disjoint fragments.

`*` in `docs/PROCESS.md` §3. The separateness proof is a gate on *formation*,
and it is worth being exact about what that does and does not buy. It does not
make the resulting value distinguishable from the plain conjunction: an author
can write that conjunction directly, and `sep_holds` and `sep_footprint` below
hold by `rfl`. What it buys is that a caller who formed a `sep` has the
separateness in hand, which is what `sep_right_survives_left_step` consumes. The
gate is on the author, not on the value.
-/
def sep (left right : NetworkAssertion agreement)
    (_separate : Separate left right) : NetworkAssertion agreement where
  holds := fun world => left.holds world ∧ right.holds world
  footprint := fun fragment => left.footprint fragment ∨ right.footprint fragment
  framed := by
    intro a b agrees
    exact and_congr
      (left.framed a b (fun fragment member => agrees fragment (Or.inl member)))
      (right.framed a b (fun fragment member => agrees fragment (Or.inr member)))

@[simp] theorem sep_holds (left right : NetworkAssertion agreement)
    (separate : Separate left right) (world : World) :
    (left.sep right separate).holds world ↔ left.holds world ∧ right.holds world :=
  Iff.rfl

@[simp] theorem sep_footprint (left right : NetworkAssertion agreement)
    (separate : Separate left right) (fragment : NetworkFragment topology) :
    (left.sep right separate).footprint fragment ↔
      left.footprint fragment ∨ right.footprint fragment :=
  Iff.rfl

/--
**A step confined to one half of a separating conjunction preserves the other.**

This is what `Separate` is *for*, and the first place in this module where it is
consumed rather than produced or permuted. `docs/PROCESS.md` §3's local checking
argument is exactly this: a send changes the sender's fragments, the receiver's
precondition names only its own, and their disjointness is what makes the
composition a library theorem instead of a whole-network re-proof.
-/
theorem sep_right_survives_left_step (left right : NetworkAssertion agreement)
    (separate : Separate left right) {before after : World}
    (touchesOnly : ∀ fragment, ¬ left.footprint fragment →
      agreement.Agrees fragment before after)
    (held : right.holds before) : right.holds after :=
  right.frame_of_disjoint_scope left.footprint separate touchesOnly held

/--
Separateness composes, so `(a * b) * c` does not re-prove disjointness from
scratch.
-/
theorem sep_separate {left right other : NetworkAssertion agreement}
    (separate : Separate left right)
    (leftOther : Separate left other) (rightOther : Separate right other) :
    Separate (left.sep right separate) other := by
  rintro fragment (inLeft | inRight)
  · exact leftOther fragment inLeft
  · exact rightOther fragment inRight

/--
An assertion that reads nothing, and therefore survives everything.

Separate from every assertion, and the honest description of a claim about the
world that does not depend on the world. It is *not* the unit of `sep` — that
would need an equivalence relation on assertions, and this module deliberately
has no entailment. `pure_sep_holds` states what is true instead.
-/
def pure (claim : Prop) : NetworkAssertion agreement where
  holds := fun _ => claim
  footprint := fun _ => False
  framed := fun _ _ _ => Iff.rfl

theorem pure_separate (claim : Prop) (assertion : NetworkAssertion agreement) :
    Separate (pure (agreement := agreement) claim) assertion :=
  fun _ member => absurd member (fun h => h)

/-- What "unit" would have meant, stated as the equivalence it actually is. -/
theorem pure_sep_holds (claim : Prop) (assertion : NetworkAssertion agreement)
    (world : World) :
    ((pure (agreement := agreement) claim).sep assertion
      (pure_separate claim assertion)).holds world ↔
      (claim ∧ assertion.holds world) :=
  Iff.rfl

end NetworkAssertion

end Grass.Process
