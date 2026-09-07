import Grass.Process.Weave.Mixin

/-!
# Independent steps, and what their order cannot change

`docs/FOUNDATION.md` law 18 forbids a specification from observing a schedule
fact, and `docs/PROCESS.md` §3 says what that means for a network: delivery
interleaving between independent senders "is a schedule fact, and a
specification that depended on it would be observing something the realization
is free to change".

To forbid depending on an interleaving you first have to say when two steps are
independent, and this module does: **when their scopes are disjoint**. That is
available because `Grass/Process/Network/Transition.lean` makes every transition
carry the fragments it may change, so independence is a question about two
predicates rather than a semantic side condition someone must supply.

## What is proved, and what is deferred

The usable content of independence is *not* that the two orders reach the same
state — it is that neither step can be seen by anything scoped inside the other.
`unaffected_by_an_independent_step` is that, and it is what a weave argument
actually consumes: an invariant living in one step's scope is untouched by every
step independent of it, whatever the schedule chose.

The **constructive diamond** — exhibiting the swapped execution — is not here,
and the reason is worth stating rather than leaving as an omission. Swapping
requires rebuilding each transition at a state it was not built at, and a
`NetworkTransition`'s constructors carry proofs about their own before-state:
`ResolvesEscrow.wasOutstanding`, `SendsEscrow.wasFresh`, `EndsInstance.wasLive`.
Whether those survive an independent step is exactly the question, and answering
it needs a lemma per constructor. `SwapsWith` names the obligation, with scope
equations that make it a genuine swap rather than "some two steps also get
there"; `independent_endpoints_agree_off_both` is the part of the diamond that
holds without it.

Claiming the diamond by defining `Independent` to include it would be the shape
of defect this layer keeps finding: a law that names what it wants instead of
proving it.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

namespace ProcessPlan

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o} {plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations}

/--
Two transitions are independent when neither may change what the other may.

Symmetric by construction — stated as mutual exclusion rather than as one-way
containment, because "independent" that held in one direction only would let a
caller conclude the wrong half.
-/
def NetworkTransition.Independent {a b c d : plan.LogicalProcessNetwork}
    (left : plan.NetworkTransition a b) (right : plan.NetworkTransition c d) : Prop :=
  ∀ fragment, left.scope fragment → ¬ right.scope fragment

namespace NetworkTransition

variable {a b c d : plan.LogicalProcessNetwork}

theorem independent_symm {left : plan.NetworkTransition a b}
    {right : plan.NetworkTransition c d}
    (independent : left.Independent right) : right.Independent left :=
  fun fragment inRight inLeft => independent fragment inLeft inRight

/--
**A step is not independent of itself, unless it changes nothing.**

Worth stating because the degenerate reading is the dangerous one: if
`Independent` admitted a step and itself, every step would commute with every
copy of itself and the relation would say nothing about scheduling. It admits
that only for a transition whose scope is empty — one that, by `touchesOnly`,
changed nothing at all.
-/
theorem self_independent_iff_scopeless {step : plan.NetworkTransition a b} :
    step.Independent step ↔ ∀ fragment, ¬ step.scope fragment := by
  constructor
  · intro independent fragment inScope
    exact independent fragment inScope inScope
  · intro scopeless fragment inScope
    exact absurd inScope (scopeless fragment)

end NetworkTransition

/-! ## What an independent step cannot disturb -/

/--
**An assertion inside one step's scope is untouched by any step independent of
it.**

The usable content of independence, and what `docs/FOUNDATION.md` law 18 needs:
a fact scoped to one process is the same whichever way the scheduler
interleaved an independent one, so a specification stated over such facts cannot
observe the interleaving.

No diamond is needed for this, which is the point — the schedule-independence
that matters is about what can be *seen*, not about reaching an identical state.
-/
theorem unaffected_by_an_independent_step
    {before after : plan.LogicalProcessNetwork}
    (step : plan.NetworkStep before after)
    (assertion : NetworkAssertion plan.agreement)
    (region : NetworkFragment plan.topology → Prop)
    (livesIn : ∀ fragment, assertion.footprint fragment → region fragment)
    (independent : ∀ fragment, step.transition.scope fragment → ¬ region fragment)
    (held : assertion.holds before) : assertion.holds after :=
  assertion.frame_of_disjoint_scope step.transition.scope
    (fun fragment inStep inFootprint =>
      independent fragment inStep (livesIn fragment inFootprint))
    step.touchesOnly held

/--
**And a mixin is untouched by every step independent of its scope.**

The same fact at `docs/PROCESS.md` §8's mixin, which is where a weave argument
consumes it: an author who declares a scope gets immunity from every step that
declares a disjoint one, without either author knowing about the other.
-/
theorem mixin_unaffected_by_independent_steps
    {before after : plan.LogicalProcessNetwork}
    (mixin : plan.WeaveInvariantMixin) (step : plan.NetworkStep before after)
    (independent : ∀ fragment, step.transition.scope fragment → ¬ mixin.Scope fragment)
    (held : mixin.assertion.holds before) : mixin.assertion.holds after :=
  mixin.frames_past_unrelated_steps step independent held

/--
**Two independent steps leave every fragment outside both alone.**

The part of the diamond that holds without reconstructing anything: after a step
and an independent step, in either order, a fragment neither of them scopes has
not moved. That is what makes "the interleaving is a schedule fact" checkable
for observers positioned outside both.
-/
theorem independent_endpoints_agree_off_both
    {first second third : plan.LogicalProcessNetwork}
    (left : plan.NetworkStep first second) (right : plan.NetworkStep second third)
    {fragment : NetworkFragment plan.topology}
    (outsideLeft : ¬ left.transition.scope fragment)
    (outsideRight : ¬ right.transition.scope fragment) :
    LogicalProcessNetworkCore.Agrees fragment first third :=
  LogicalProcessNetworkCore.agrees_trans fragment first second third
    (left.touchesOnly fragment outsideLeft)
    (right.touchesOnly fragment outsideRight)

/--
The constructive diamond, named rather than assumed.

Swapping two independent steps means rebuilding each at a state it was not built
at, and every interesting constructor of `NetworkTransition` carries a proof
about its own before-state — `ResolvesEscrow.wasOutstanding`,
`SendsEscrow.wasFresh`, `EndsInstance.wasLive`. Whether those survive an
independent step is precisely the question a diamond answers, and it needs one
lemma per constructor rather than a definition.

The scope equations are what make this a *swap* rather than "some two steps also
get there": the reordered execution must run the same two transitions, and a
transition's scope is the only handle this layer has on which one it is. An
earlier draft omitted them and asserted merely that some pair of steps reached
`third` from `first`, which is satisfied by almost anything and mentions neither
`left` nor `right` — the unused-variable linter is what caught it.

Stated as an obligation a later module discharges, because defining
`Independent` to include the swap would be assuming the theorem.
-/
def SwapsWith {first second third : plan.LogicalProcessNetwork}
    (left : plan.NetworkStep first second) (right : plan.NetworkStep second third) : Prop :=
  ∃ (middle : plan.LogicalProcessNetwork)
    (swappedRight : plan.NetworkStep first middle)
    (swappedLeft : plan.NetworkStep middle third),
    (∀ fragment, swappedRight.transition.scope fragment ↔ right.transition.scope fragment) ∧
    (∀ fragment, swappedLeft.transition.scope fragment ↔ left.transition.scope fragment)

/--
Where the diamond *would* be usable, and where it is not needed.

If two independent steps swap, an observer outside both scopes sees the same
thing along the reordered execution — which is
`independent_endpoints_agree_off_both` applied to the other order, using the
scope equations to know the reordered steps are still outside that fragment.

So a consumer that reads only outside both scopes never needs the diamond, and
one that reads inside a scope was not schedule-independent to begin with. That
is why `unaffected_by_an_independent_step` rather than a diamond is what this
layer exports, and why the diamond's absence costs nothing here.
-/
theorem swapped_execution_agrees_off_both
    {first second third : plan.LogicalProcessNetwork}
    {left : plan.NetworkStep first second} {right : plan.NetworkStep second third}
    (swap : SwapsWith left right)
    {fragment : NetworkFragment plan.topology}
    (outsideLeft : ¬ left.transition.scope fragment)
    (outsideRight : ¬ right.transition.scope fragment) :
    LogicalProcessNetworkCore.Agrees fragment first third := by
  obtain ⟨_, swappedRight, swappedLeft, rightScope, leftScope⟩ := swap
  exact independent_endpoints_agree_off_both swappedRight swappedLeft
    (fun inSwapped => outsideRight ((rightScope fragment).mp inSwapped))
    (fun inSwapped => outsideLeft ((leftScope fragment).mp inSwapped))

end ProcessPlan

end Grass.Process
