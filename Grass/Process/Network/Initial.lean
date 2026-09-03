import Grass.Process.Weave.Mixin

/-!
# Where a network starts

Three modules name this gap and defer to it. `Grass/Process/Weave/Mixin.lean`'s
`HoldsInitially` says §8's `initial` field "needs `ExactInitialNetwork`, and
there is no initial-network relation yet". `docs/PROCESS.md` §3's
`ProcessNetworkAdequate.initial` asks for
`Nonempty (ExactInitialNetworkAndRootRun plan input)`, and §8's
`WeaveInvariantMixin.initial` for the same object. This module is it.

## What "exact" means, and why every clause is a `∀`

An initial network is not merely *a* network the program could be in. It is the
one it starts in, so every fragment has to be pinned: the root is live at a
state its own protocol calls initial, holding the demands that start issued;
nothing else is live; no channel holds anything; no session has delivered; the
trace holds exactly what starting emitted; and the nominal history holds the
root's generation and is reachable from empty.

A relation that pinned only the root would be satisfied by a network with
arbitrary escrow, which is the shape §3's "exact" is guarding against — an
invariant proved of "the initial network" would then be proved of a network the
program never starts in.

## The payoff

`initial_is_wellformed` is why the exactness is worth the fields. Four of
`WellFormed`'s six clauses are discharged *because* nothing else exists yet:
there is no second instance to violate root uniqueness, no recorded parent to
be invalid, and no escrow to hold a reroute that never lands. The remaining two
come from the root's own record.

That makes the initial network a place a weave argument can start:
`WeaveInvariantMixin.preserved_by_every_step` carries an invariant along any
execution, and `HoldsInitially` is what puts it at the beginning.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

namespace ProcessPlan

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o} (plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations)

/--
The network a request starts in.

`docs/PROCESS.md` §3's `ExactInitialNetwork`. `rootSlot` is a field rather than
an existential because four other clauses have to refer to it — "nothing else is
live" is a statement about every other slot, and a slot bound existentially in
one clause is not available to the next.
-/
structure ExactInitialNetwork
    (request : (plan.topology.protocol plan.topology.root).Request)
    (network : plan.LogicalProcessNetwork) where
  /-- Which slot the root occupies. -/
  rootSlot : plan.topology.InstanceId plan.topology.root
  /-- The incarnation in it. -/
  root : ProcessInstance plan.topology
  /-- It is there. -/
  rootPresent : network.instances plan.topology.root rootSlot = some root
  /-- Of the root kind. -/
  rootKind : root.kind = plan.topology.root
  /--
  **At a state, demand bag and observation segment its own protocol calls
  initial.**

  All three at once, because `ProcessSpec.Initial` relates all three: a network
  that started the root at a permitted state while inventing its outstanding
  demands would satisfy a weaker clause and be wrong.
  -/
  rootEmitted : ObservationSegment (plan.topology.protocol plan.topology.root).Observation
  rootInitial : (plan.topology.protocol plan.topology.root).Initial request
    (rootKind ▸ root.localState) (rootKind ▸ root.outstanding) rootEmitted
  /--
  And the pending trace holds exactly the projection of what starting emitted.

  The same seam as `StepsLocally.emittedIsProjected`: a role's observations
  reach the network through `ProcessGraph.observeAt` and not otherwise, so a
  start cannot put anything in the trace the root did not observe.

  `pending`, not `observations`, since `NetworkFragment.pending` split the two:
  a start *produces*, and nothing is committed until a driver commits it.
  -/
  pendingProjected : network.pending =
    rootEmitted.filterMap (plan.topology.observeAt plan.topology.root)
  /--
  **And nothing has been committed.**

  The committed trace at a start is empty, because only `commit` moves it and no
  commit has happened. Without this field a "start" could begin with an arbitrary
  history of published observations, which is exactly the fabrication
  `ExactInitialNetwork` exists to exclude — and it was invisible while one trace
  served both roles.
  -/
  nothingCommitted : network.observations = []
  /-- Started with the request it was given. -/
  rootRequest : rootKind ▸ root.request = request
  /-- Running. -/
  rootRunning : root.lifecycle = .running
  /-- And it is the root: no parent, and never had one. -/
  rootParentage : root.IsRoot
  /-- Its generation was allocated. -/
  rootAllocated : root.ref.Allocated network.usedNominals
  /-- **And nothing else is live.** -/
  onlyTheRoot : ∀ kind slot incarnation, network.instances kind slot = some incarnation →
    ∃ sameKind : kind = plan.topology.root, sameKind ▸ slot = rootSlot
  /-- **Nothing is in flight, on any session of any edge.** -/
  nothingInFlight : ∀ edge session, network.inFlight edge session = EscrowLedger.empty
  /-- **Every session is open and has delivered nothing.** -/
  sessionsFresh : ∀ edge session, network.sessions edge session = ⟨.open, 0⟩
  /--
  **And the nominal history is reachable from empty.**

  `docs/FOUNDATION.md` law 22: freshness is absence from the monotone history.
  A start whose history was arbitrary could claim a generation fresh that a
  previous run had used, so the history has to begin where histories begin.
  -/
  historyFromEmpty : NominalHistory.Reaches NominalHistory.initial network.usedNominals

/--
The obligation §8's `WeaveInvariantMixin.initial` names, now with something to
name it against.

`Grass/Process/Weave/Mixin.lean`'s `HoldsInitially` takes an arbitrary
`Initial` predicate because there was no initial-network relation to take. This
is that predicate.
-/
def HoldsAtEveryStart (assertion : NetworkAssertion plan.agreement) : Prop :=
  ∀ request network, plan.ExactInitialNetwork request network → assertion.holds network

/--
**A network is a start for at most one request.**

`onlyTheRoot` forces one live slot, `rootPresent` forces one incarnation in it,
and `rootRequest` reads the request off that incarnation — so two starts of the
same network agree.

Worth stating because `Grass/Process/Network/Progress.lean`'s `startIsInitial`
quantifies the request existentially, and a docstring there once called that a
choice needing a ruling: "a plan started with two different requests has two
different progress arguments, and nothing here says which one a measure is
about". A reviewer proved the network says which. There is nothing to rule on.
-/
theorem request_is_determined {left right : (plan.topology.protocol plan.topology.root).Request}
    {network : plan.LogicalProcessNetwork}
    (first : plan.ExactInitialNetwork left network)
    (second : plan.ExactInitialNetwork right network) : left = right := by
  obtain ⟨sameKind, sameSlot⟩ :=
    first.onlyTheRoot plan.topology.root second.rootSlot second.root second.rootPresent
  have sameSlot' : second.rootSlot = first.rootSlot := by
    cases sameKind
    exact sameSlot
  have sameRoot : first.root = second.root := by
    have found := second.rootPresent
    rw [sameSlot'] at found
    exact Option.some.inj (first.rootPresent.symm.trans found)
  have transportIsIrrelevant : ∀ (left' right' : ProcessInstance plan.topology)
      (leftKind : left'.kind = plan.topology.root)
      (rightKind : right'.kind = plan.topology.root), left' = right' →
      (leftKind ▸ left'.request : (plan.topology.protocol plan.topology.root).Request)
        = rightKind ▸ right'.request := by
    intro left' right' _ _ same
    subst same
    rfl
  exact (first.rootRequest.symm.trans
    (transportIsIrrelevant first.root second.root first.rootKind second.rootKind
      sameRoot)).trans second.rootRequest

namespace ExactInitialNetwork

variable {plan} {request : (plan.topology.protocol plan.topology.root).Request}
  {network : plan.LogicalProcessNetwork}
  (start : plan.ExactInitialNetwork request network)

include start

/-- **Nothing has been received anywhere.** -/
theorem nothing_delivered (edge : plan.topology.ChannelKind)
    (session : plan.topology.ChannelId edge) :
    (network.sessions edge session).delivered = 0 := by
  rw [start.sessionsFresh edge session]

/-- **And every channel is open.** -/
theorem every_session_open (edge : plan.topology.ChannelKind)
    (session : plan.topology.ChannelId edge) :
    (network.sessions edge session).status = .open := by
  rw [start.sessionsFresh edge session]

/-- **No occurrence has been created.** -/
theorem nothing_created (edge : plan.topology.ChannelKind)
    (session : plan.topology.ChannelId edge) :
    (network.inFlight edge session).created = [] := by
  rw [start.nothingInFlight edge session]
  rfl

/-- **The only live instance is the root's.** -/
theorem the_root_is_alone {kind : plan.topology.ProcessKind}
    {slot : plan.topology.InstanceId kind} {incarnation : ProcessInstance plan.topology}
    (found : network.instances kind slot = some incarnation) :
    ∃ sameKind : kind = plan.topology.root, sameKind ▸ slot = start.rootSlot :=
  start.onlyTheRoot kind slot incarnation found

/-- **And no instance has a parent**, because there is nobody to be one. -/
theorem nothing_has_a_parent {kind : plan.topology.ProcessKind}
    {slot : plan.topology.InstanceId kind} {incarnation : ProcessInstance plan.topology}
    (found : network.instances kind slot = some incarnation)
    {parentKind : plan.topology.ProcessKind} {parent : plan.topology.ProcessRef parentKind}
    (claimed : incarnation.parentage.knownParent = some ⟨parentKind, parent⟩) :
    plan.topology.maySpawn parentKind incarnation.kind := by
  obtain ⟨sameKind, sameSlot⟩ := start.the_root_is_alone found
  subst sameKind
  simp only at sameSlot
  subst sameSlot
  rw [start.rootPresent] at found
  injection found with isRoot
  have noParent : incarnation.parentage.knownParent = none := by
    rw [← isRoot]
    exact ProcessParentage.knownParent_eq_none_of_isRoot start.rootParentage
  rw [noParent] at claimed
  exact absurd claimed (by simp)

/--
**An exact initial network is well formed.**

Four of `WellFormed`'s six clauses hold *because* nothing else exists yet — that
is what the exactness buys, and it is why a relation pinning only the root would
not have been enough.

* `rootUnique` — there is one live instance, so two roots are in one slot.
* `parentageValid` — nothing has a parent, so no recorded parenthood is invalid.
* `reroutesLand` — every ledger is empty, so no occurrence is rerouted.
* `lifecyclesWitnessed` — the only instance is `running`, and the clause
  constrains `terminated` endings.

The other two come from the root's own record: `slotsAgree` from `SlotsAgree`
being about the slot the root is stored under, and `nominalsAllocated` from
`rootAllocated`.
-/
theorem initial_is_wellformed
    (slotsAgree : network.SlotsAgree) : network.WellFormed where
  slotsAgree := slotsAgree
  lifecyclesWitnessed := by
    intro kind slot incarnation found result terminated
    obtain ⟨sameKind, sameSlot⟩ := start.the_root_is_alone found
    subst sameKind
    simp only at sameSlot
    subst sameSlot
    rw [start.rootPresent] at found
    injection found with isRoot
    subst isRoot
    rw [start.rootRunning] at terminated
    exact absurd terminated (by simp)
  rootUnique := by
    intro leftSlot rightSlot leftInstance rightInstance leftFound rightFound _ _
    obtain ⟨_, leftIsRoot⟩ := start.the_root_is_alone leftFound
    obtain ⟨_, rightIsRoot⟩ := start.the_root_is_alone rightFound
    simp only at leftIsRoot rightIsRoot
    rw [leftIsRoot, rightIsRoot]
  parentageValid := by
    intro kind slot incarnation found parentKind parent claimed
    exact start.nothing_has_a_parent found claimed
  nominalsAllocated := by
    intro kind slot incarnation found
    obtain ⟨sameKind, sameSlot⟩ := start.the_root_is_alone found
    subst sameKind
    simp only at sameSlot
    subst sameSlot
    rw [start.rootPresent] at found
    injection found with isRoot
    subst isRoot
    exact start.rootAllocated
  reroutesLand := by
    intro edge session occurrence destination rerouted
    rw [start.nothingInFlight edge session] at rerouted
    exact absurd rerouted (by simp [EscrowLedger.empty])

end ExactInitialNetwork

/-! ## What a weave argument was waiting for -/

variable {plan}

/--
**An invariant that holds at every start and is preserved by every step holds
along every execution from a start.**

This is what `Grass/Process/Weave/Mixin.lean` was building toward and could not
state. `preserved_by_every_step` carries an invariant across one step and
`all_preserved_along` across an execution, but neither says anything about where
the execution began — so an invariant could be "preserved" forever without ever
having been true.

`docs/PROCESS.md` §8's `WeaveInvariantMixin.initial` is `HoldsAtEveryStart`, and
this is the two composed. Note what the mixin author supplies: `affected`, and a
proof that the assertion holds at a start. Everything between is framing.
-/
theorem holds_along_every_execution_from_a_start (mixin : plan.WeaveInvariantMixin)
    (atStart : plan.HoldsAtEveryStart mixin.assertion)
    {request : (plan.topology.protocol plan.topology.root).Request}
    {network final : plan.LogicalProcessNetwork}
    (start : plan.ExactInitialNetwork request network)
    (execution : plan.StepsTo network final) : mixin.assertion.holds final := by
  induction execution with
  | still => exact atStart request network start
  | more _ step ih => exact mixin.preserved_by_every_step step ih

/-- And a whole family of them, which is what §8's aggregate consumes. -/
theorem family_holds_along_every_execution_from_a_start
    (family : plan.WeaveInvariantFamily)
    (atStart : ∀ key, plan.HoldsAtEveryStart (family.mixin key).assertion)
    {request : (plan.topology.protocol plan.topology.root).Request}
    {network final : plan.LogicalProcessNetwork}
    (start : plan.ExactInitialNetwork request network)
    (execution : plan.StepsTo network final) :
    ∀ key, (family.mixin key).assertion.holds final :=
  fun key => holds_along_every_execution_from_a_start (family.mixin key) (atStart key)
    start execution

end ProcessPlan

end Grass.Process
