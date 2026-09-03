import Grass.Process.Weave.Mixin
import Tests.Process.TransitionFixtures

/-!
# A cross-process invariant that frames itself

`Grass/Process/Weave/Mixin.lean` claims `docs/PROCESS.md` §8's `frame` field is
a *consequence* of the footprint discipline and the transition-scope discipline
rather than an obligation an author discharges. This file is that claim at a
concrete mixin and a concrete step.

* `routeTableStable` is a mixin over the M2 fixture plan: the route table is
  empty, scoped to the route-table fragment. Its `affected` — the author's only
  real obligation — is discharged by the *topology*: `serverGraph` gives both
  roles `readOnly` access to the route table, so no step can write it.
* `receive_does_not_disturb_it` frames it past the receive step from
  `Tests/Process/TransitionFixtures.lean` with no framing proof of its own. The
  author of the mixin never mentioned the receive, and the author of the receive
  never mentioned the mixin.
* `escrow_reading_mixin_is_not_route_table_scoped` is the teeth. Without
  `withinScope`, framing would be *unsound* rather than merely weak: an assertion
  reading a fragment the step changed would be claimed to survive it.

## This fixture found a defect in the transition family

Writing it is what showed that no constructor of `NetworkTransition` could touch
a shared region at all — `processStep`'s scope named the instance slot and the
observation trace and stopped. A weave mixin about shared state would then have
framed past every step in the program, vacuously and wrongly, and nothing in the
transition module or its own fixture would have noticed, because a family that
touches fewer fragments satisfies its scope law more easily.

`StepsLocally` now carries the regions a step wrote and requires write access
for each. `no_step_writes_the_route_table` below is what that buys: an
immutability fact from `ProcessGraph.sharedAccess` becomes a fact about every
execution.
-/

namespace Grass.Process.Tests.Weave

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.Transition (serverPlan beforeReceive afterReceive receiveAsStep)

/-! ## No step of this plan writes the route table -/

/--
**A transition that touches a region is a process step that was allowed to
write it.**

The bridge from `ProcessGraph.sharedAccess` — a static declaration — to a fact
about every step of every execution. Only `processStep` names a region in its
scope, and only for regions its own role may write.
-/
theorem touching_a_region_needs_write_access
    {before after : serverPlan.LogicalProcessNetwork}
    (transition : serverPlan.NetworkTransition before after)
    (region : serverTopology.SharedRegion)
    (touches : transition.scope (.region region)) :
    ∃ kind, (serverTopology.sharedAccess kind region).mayWrite = true := by
  cases transition with
  | processStep kind _ _ written _ _ _ step =>
    rcases touches with isSlot | ⟨_, isObservations⟩ | ⟨named, wrote, isRegion⟩
    · exact absurd isSlot (by simp)
    · exact absurd isObservations (by simp)
    · refine ⟨kind, ?_⟩
      have same : named = region := by
        injection isRegion with same
        exact same.symm
      rw [← same]
      exact step.writesPermitted named wrote
  | _ => exact absurd touches (by simp [ProcessPlan.NetworkTransition.scope])

/--
**So no step writes the route table.**

`Tests/Process/M2GraphFixtures.lean` proves `routeTable_immutable` — neither
role may write it. This lifts that from a statement about the graph to a
statement about every transition of every execution.
-/
theorem no_step_writes_the_route_table
    {before after : serverPlan.LogicalProcessNetwork}
    (transition : serverPlan.NetworkTransition before after)
    (touches : transition.scope (.region .routeTable)) : False := by
  obtain ⟨kind, mayWrite⟩ :=
    touching_a_region_needs_write_access transition .routeTable touches
  cases kind <;> exact absurd mayWrite (by decide)

/-! ## The mixin -/

/-- The invariant: the route table is empty. -/
noncomputable def routeTableEmpty : NetworkAssertion serverPlan.agreement where
  holds := fun network => network.shared .routeTable = ⟨[]⟩
  footprint := fun fragment => fragment = .region .routeTable
  framed := by
    intro left right agrees
    have same : left.shared .routeTable = right.shared .routeTable := agrees _ rfl
    rw [same]

/--
The mixin.

Three fields, and `affected` is the only one with content — discharged here
because its hypothesis is unsatisfiable at this plan. That is not a cheat: it is
the topology's read-only declaration doing exactly the work
`docs/PROCESS.md` §3 says shared-state capabilities are for.
-/
noncomputable def routeTableStable : serverPlan.WeaveInvariantMixin where
  Scope := fun fragment => fragment = .region .routeTable
  assertion := routeTableEmpty
  withinScope := fun _ inFootprint => inFootprint
  affected := by
    intro before after step touches _
    obtain ⟨fragment, inScope, inStep⟩ := touches
    rw [inScope] at inStep
    exact absurd inStep (fun t => no_step_writes_the_route_table step.transition t)

/-! ## Framing, without a framing proof -/

/-- The invariant holds before the step, so nothing below is vacuous. -/
theorem route_table_is_empty_before : routeTableStable.assertion.holds beforeReceive := rfl

/--
**The receive step does not disturb it.**

The receive was written before this mixin existed and mentions nothing about
route tables; this mixin says nothing about escrow. The framing comes from the
step's own scope and the assertion's own footprint, which is §8's `frame` field
derived rather than supplied.
-/
theorem receive_does_not_disturb_it :
    routeTableStable.assertion.holds afterReceive := by
  refine routeTableStable.frames_past_unrelated_steps receiveAsStep ?_
    route_table_is_empty_before
  intro fragment inStep inScope
  rw [inScope] at inStep
  exact no_step_writes_the_route_table receiveAsStep.transition inStep

/--
The same, without asking which case applies.

`preserved_by_every_step` is the form a weave argument uses: it does not need to
know whether the step touched the scope, because one of the two halves always
covers it.
-/
theorem receive_preserves_it : routeTableStable.assertion.holds afterReceive :=
  routeTableStable.preserved_by_every_step receiveAsStep route_table_is_empty_before

/-- And it survives a whole execution, not just one step. -/
theorem survives_any_execution {final : serverPlan.LogicalProcessNetwork}
    (execution : serverPlan.StepsTo beforeReceive final) :
    routeTableStable.assertion.holds final := by
  induction execution with
  | still => exact route_table_is_empty_before
  | more _ step ih => exact routeTableStable.preserved_by_every_step step ih

/-! ## And what `withinScope` rejects -/

/-- An assertion about escrow rather than about the route table. -/
noncomputable def escrowAssertion : NetworkAssertion serverPlan.agreement where
  holds := fun network => (network.inFlight () Channel.wire).created = []
  footprint := fun fragment => fragment = .escrow () Channel.wire
  framed := by
    intro left right agrees
    have same : left.inFlight () Channel.wire = right.inFlight () Channel.wire :=
      agrees _ rfl
    rw [same]

/--
**A mixin cannot claim the route-table scope while reading escrow.**

The teeth of `withinScope`, and the reason `frames_past_unrelated_steps` is
sound rather than merely convenient. Without this field a mixin could declare a
narrow scope, read a fragment outside it, and be "framed" past a step that
changed exactly that fragment — which makes the theorem false, not weak.

Stated over an arbitrary mixin, because it is a property of the type.
-/
theorem escrow_reading_mixin_is_not_route_table_scoped
    (mixin : serverPlan.WeaveInvariantMixin)
    (readsEscrow : mixin.assertion = escrowAssertion)
    (claimsRouteTable :
      mixin.Scope = fun fragment => fragment = .region .routeTable) : False := by
  have inFootprint : mixin.assertion.footprint (.escrow () Channel.wire) := by
    rw [readsEscrow]
    rfl
  have inScope := mixin.withinScope _ inFootprint
  rw [claimsRouteTable] at inScope
  exact absurd inScope (by simp)

end Grass.Process.Tests.Weave
