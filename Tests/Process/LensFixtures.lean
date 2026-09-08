import Grass.Process.Weave.Lens
import Tests.Process.WeaveFixtures

/-!
# A refinement lens at a concrete plan

`Grass/Process/Weave/Lens.lean` proves `docs/PROCESS.md` §8's generic contextual
theorem — a step inside a lens preserves every invariant outside it. That
theorem is worth nothing if no lens selects any step, so this file builds one
that does.

`connectionLens` refines the connection role and the channel it owns.
`routeTableStable` — from `Tests/Process/WeaveFixtures.lean`, written before
lenses existed and mentioning none — is outside it. `the_receive_is_inside` and
`the_route_table_mixin_survives_the_refinement` are the two halves: a real step
of the selected subgraph, and a real invariant framed past it by an author who
never heard of either.

## What makes this non-vacuous

Two things could have made it hollow and neither does.

The lens could have selected nothing: `Selects` demands a transition's *whole*
scope be interior, so a lens that owns a role but not the channels it uses
selects no channel step at all. `connectionLens` owns the wire escrow for
exactly that reason, and `the_receive_is_inside` is the check.

The mixin could have been trivially exterior for the wrong reason — if
`Interior` were empty, every mixin would be exterior and the framing would come
from the lens owning nothing. `the_lens_owns_something` rules that out.
-/

namespace Grass.Process.Tests.Lens

open Grass.Process
open Grass.Specification
open Grass.Process.Tests
open Grass.Process.Tests.Transition (serverPlan beforeReceive afterReceive receiveStep
  receiveAsStep receive_scope_is_the_session)
open Grass.Process.Tests.Weave (routeTableStable route_table_is_empty_before)
open Grass.Process.Tests.Channel (wire)

/-! ## The lens -/

/--
A refinement of the connection role and the channel it owns — both its escrow
and its session cursor, since a delivery moves each.

The coupling fields are discharged by case analysis on `Role`, which is what
they are for: an `Interior` chosen to suit a theorem would fail one of them.
-/
def connectionLens : serverPlan.ProcessRefinementLens where
  Selected := fun role => role = .connection
  selectsSomething := ⟨.connection, rfl⟩
  Interior := fun fragment =>
    fragment = .escrow () wire ∨ fragment = .session () wire ∨
      ∃ slot, fragment = .instanceState .connection slot
  selectedStateInterior := by
    rintro kind slot rfl
    exact Or.inr (Or.inr ⟨slot, rfl⟩)
  unselectedStateExterior := by
    rintro kind slot notConnection (isEscrow | isSession | ⟨other, isConnection⟩)
    · exact absurd isEscrow (by simp)
    · exact absurd isSession (by simp)
    · injection isConnection with sameKind
      exact notConnection sameKind
  interiorChannelsTouchTheSelection := by
    rintro edge session (isEscrow | isSession | ⟨_, isInstance⟩)
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact absurd isInstance (by simp)
  interiorRegionsAreWritable := by
    rintro region (isEscrow | isSession | ⟨_, isInstance⟩)
    · exact absurd isEscrow (by simp)
    · exact absurd isSession (by simp)
    · exact absurd isInstance (by simp)
  refinedRequirements := RequirementSet.empty
  refinementOnlyAdds := RequirementSet.Covers.refl _

/--
**The lens owns something.**

Without this the framing below would be true for the empty reason: a lens with
an empty interior frames everything because it selects nothing.
-/
theorem the_lens_owns_something : connectionLens.Interior (.escrow () wire) := Or.inl rfl

/-- And it does not own the route table. -/
theorem the_lens_does_not_own_the_route_table :
    ¬ connectionLens.Interior (.region .routeTable) := by
  rintro (isEscrow | isSession | ⟨_, isInstance⟩)
  · exact absurd isEscrow (by simp)
  · exact absurd isSession (by simp)
  · exact absurd isInstance (by simp)

/-! ## A real step inside it -/

/--
**The receive is a step of the selected subgraph.**

Its whole scope — the wire escrow — is interior. This is the check that
`Selects` is satisfiable at all: it demands the *whole* scope, so a lens that
owned the connection role but not its channel would select no channel step.
-/
theorem the_receive_is_inside : connectionLens.Selects receiveStep := by
  intro fragment inScope
  rcases (receive_scope_is_the_session fragment).mp inScope with isEscrow | isSession
  · exact Or.inl isEscrow
  · exact Or.inr (Or.inl isSession)

/-! ## And an invariant outside it, framed -/

/-- The route-table mixin lives entirely outside the lens. -/
theorem the_route_table_mixin_is_exterior : connectionLens.Exterior routeTableStable := by
  intro fragment inScope
  have isRouteTable : fragment = .region .routeTable := inScope
  rw [isRouteTable]
  exact the_lens_does_not_own_the_route_table

/--
**§8's generic contextual theorem, at a step and an invariant that have never
met.**

`routeTableStable` was written against a receive step in
`Tests/Process/WeaveFixtures.lean` and says nothing about refinement;
`connectionLens` says nothing about route tables. The framing is the lens's
interior and the assertion's footprint being disjoint, and nothing else.
-/
theorem the_route_table_mixin_survives_the_refinement :
    routeTableStable.assertion.holds afterReceive :=
  ProcessPlan.ProcessRefinementLens.frames_every_exterior_mixin
    the_route_table_mixin_is_exterior receiveAsStep the_receive_is_inside
    route_table_is_empty_before

/--
**And the exterior is preserved fragment-by-fragment, not only assertion-wise.**

The stronger form: a later refinement of the listener role starts from exactly
the state it would have had without this one.
-/
theorem the_exterior_did_not_move (fragment : NetworkFragment serverTopology)
    (outside : ¬ connectionLens.Interior fragment) :
    LogicalProcessNetworkCore.Agrees fragment beforeReceive afterReceive :=
  ProcessPlan.ProcessRefinementLens.interior_steps_preserve_the_exterior
    (lens := connectionLens) beforeReceive afterReceive
    (.more .still receiveAsStep the_receive_is_inside) fragment outside

/-- In particular the listener's own state did not move. -/
theorem the_listener_did_not_move (slot : serverTopology.InstanceId .listener) :
    beforeReceive.instances .listener slot = afterReceive.instances .listener slot := by
  refine ProcessPlan.ProcessRefinementLens.unselected_state_is_untouched
    receiveAsStep the_receive_is_inside .listener slot ?_
  intro isConnection
  have isSame : Role.listener = Role.connection := isConnection
  exact absurd isSame (by decide)

/-! ## Two lenses that do not know about each other -/

/-- A second refinement, of the listener role. -/
def listenerLens : serverPlan.ProcessRefinementLens where
  Selected := fun role => role = .listener
  selectsSomething := ⟨.listener, rfl⟩
  Interior := fun fragment => ∃ slot, fragment = .instanceState .listener slot
  selectedStateInterior := by
    rintro kind slot rfl
    exact ⟨slot, rfl⟩
  unselectedStateExterior := by
    rintro kind slot notListener ⟨other, isListener⟩
    injection isListener with sameKind
    exact notListener sameKind
  interiorChannelsTouchTheSelection := by
    rintro edge session ⟨_, isInstance⟩
    exact absurd isInstance (by simp)
  interiorRegionsAreWritable := by
    rintro region ⟨_, isInstance⟩
    exact absurd isInstance (by simp)
  refinedRequirements := RequirementSet.empty
  refinementOnlyAdds := RequirementSet.Covers.refl _

/-- **They are disjoint.** -/
theorem the_two_lenses_are_disjoint :
    ProcessPlan.ProcessRefinementLens.Disjoint connectionLens listenerLens := by
  rintro fragment (isEscrow | isSession | ⟨_, isConnection⟩) ⟨_, isListener⟩
  · rw [isEscrow] at isListener
    exact absurd isListener (by simp)
  · rw [isSession] at isListener
    exact absurd isListener (by simp)
  · rw [isConnection] at isListener
    injection isListener with sameKind
    exact absurd sameKind (by decide)

/--
**So neither reopens the other's proof.**

§8's graphics-and-disk sentence at this plan: an invariant belonging to the
listener refinement survives every step of the connection refinement, with no
ordering between them and no joint proof term.
-/
theorem the_listener_refinement_is_not_reopened
    (mixin : serverPlan.WeaveInvariantMixin)
    (belongsToListener : ∀ fragment, mixin.Scope fragment → listenerLens.Interior fragment)
    (held : mixin.assertion.holds beforeReceive) :
    mixin.assertion.holds afterReceive :=
  ProcessPlan.ProcessRefinementLens.disjoint_lenses_do_not_reopen_each_other
    the_two_lenses_are_disjoint belongsToListener receiveAsStep the_receive_is_inside held

/--
**And neither may emit without the other knowing.**

`at_most_one_lens_may_emit` at these two: since they are disjoint, at most one
owns the *produced* trace, so at most one refinement can change what the program
says. Here neither does — the receive is silent — which is why the listener
refinement can be written without an origin-preservation argument.

`.pending`, not `.observations`. A reviewer pointed out that the earlier version
of this theorem was negative about a class no receive could ever be in: after the
trace split only `commit` declares `.observations`, so "this receive does not
declare it" was true of every non-commit step of every plan and checked nothing.
`.pending` is the fragment an emitting step actually declares.
-/
theorem the_connection_refinement_is_silent : ¬ receiveStep.scope .pending := by
  intro emits
  rcases (receive_scope_is_the_session _).mp emits with isEscrow | isSession
  · exact absurd isEscrow (by simp)
  · exact absurd isSession (by simp)

end Grass.Process.Tests.Lens
