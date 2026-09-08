import Grass.Process.Network.WellFormedness
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

`initial_is_wellformed` is why the exactness is worth the fields. Most of
`WellFormed`'s clauses are discharged *because* nothing else exists yet: there is
no second instance to violate root uniqueness, no recorded parent to be invalid,
and no escrow to hold a reroute that never lands, an occurrence on the wrong
session, or two entries sharing a nominal. Two more come from the root's own
record: `nominalsAllocated` from `rootAllocated`, and `slotsAgree` from
`rootSlotAgrees`, which §10.106 added after a reviewer noticed the theorem was
taking that clause as a hypothesis instead. And `sharedInvariantHolds` comes from
neither, but from `ExactInitialNetwork`'s own `sharedInvariantAtStart`, which is
a field an author supplies — the theorem's own docstring below sets the three
groups out in order.

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
  **And it is stored where its own reference says it is.**

  `ProcessRef` has an `instanceId` as well as a generation, and `rootKind`
  constrains only the kind — so a "start" could place the root in one slot while
  its reference names another, and `LogicalProcessNetworkCore.SlotsAgree` would
  fail at the very first network of the run.

  `ProcessPlan.Spawns.slotAgrees` is this field at a spawn, and it was added
  because local adversarial review built exactly that step. A reviewer noticed
  that `initial_is_wellformed` took `SlotsAgree` as a *hypothesis* rather than
  discharging it, which is what a missing field looks like from the caller's
  side. With this, the hypothesis is gone.
  `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.106.
  -/
  rootSlotAgrees : rootKind ▸ root.ref.instanceId = rootSlot
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
  **And every shared region starts holding what the graph requires.**

  The clause `LogicalProcessNetworkCore.SharedInvariantHolds` needs at a start,
  and the one thing about shared state a *start* can be asked. `sharedUpdate`
  bounds how a region moves and `sharedUpdatePreserves` carries the invariant
  across a step, so an execution keeps it — but only if it begins with it, and
  nothing else here says what a region initially holds.

  This is `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.106's shape again: a clause
  the theorem below would otherwise have to take as a hypothesis is a missing
  field, seen from the caller's side. A graph with no regions discharges it by
  `elim`.
  -/
  sharedInvariantAtStart : ∀ region,
    plan.topology.sharedInvariant region (network.shared region)
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

Most of `WellFormed`'s clauses hold *because* nothing else exists yet — that is
what the exactness buys, and it is why a relation pinning only the root would not
have been enough. Three do not, and they are listed after the six that do.

* `rootUnique` — there is one live instance, so two roots are in one slot.
* `parentageValid` — nothing has a parent, so no recorded parenthood is invalid.
* `reroutesLand` — every ledger is empty, so no occurrence is rerouted.
* `occurrencesOnTheirSession` — every ledger is empty, so nothing is in the wrong
  one.
* `identitiesDistinct` — every ledger is empty, so no two entries share a nominal.
* `lifecyclesWitnessed` — the only instance is `running`, and the clause
  constrains `terminated` endings.

`sharedInvariantHolds` is the exception to both halves: it comes from neither
emptiness nor the root, but from `ExactInitialNetwork.sharedInvariantAtStart`,
which is a field an author supplies. §10.128 added the clause and this
enumeration did not move.

The other two come from the root's own record: `nominalsAllocated` from
`rootAllocated`, and `slotsAgree` from `rootSlotAgrees` together with
`the_root_is_alone`.

`slotsAgree` was a *hypothesis* of this theorem until §10.106, because
`ExactInitialNetwork` had no field tying the root's own `ref.instanceId` to
`rootSlot` — the field `ProcessPlan.Spawns.slotAgrees` is at a spawn. A reviewer
found it by reading the signature: a clause passed in rather than discharged is
what a missing field looks like from the caller's side.
-/
theorem initial_is_wellformed : network.WellFormed where
  occurrencesOnTheirSession := by
    intro edge session occurrence held
    rw [start.nothingInFlight edge session] at held
    exact absurd held List.not_mem_nil
  identitiesDistinct := by
    intro edge session first _ held _ _
    rw [start.nothingInFlight edge session] at held
    exact absurd held List.not_mem_nil
  sharedInvariantHolds := start.sharedInvariantAtStart
  slotsAgree := by
    intro kind slot incarnation found
    obtain ⟨sameKind, sameSlot⟩ := start.the_root_is_alone found
    subst sameKind
    simp only at sameSlot
    subst sameSlot
    rw [start.rootPresent] at found
    injection found with isRoot
    subst isRoot
    exact ⟨start.rootKind, start.rootSlotAgrees⟩
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

/--
A slot holds an instance that records no current parent and is not dead.

The invariant `execution_holds_an_unkilled_root` carries. Three conjuncts, and
each does work: the slot is *occupied*, by an instance with *no current parent*,
which is *not dead*. `Tests/Process/PreservationFixtures.lean` falsifies the
first at several worlds and the third at `sentWithDeadSender`. A detached child
satisfies the second and can fail the third —
`Tests/Process/PreservationFixtures.lean`'s `a_corpse_may_be_orphaned` — so this
is deliberately not "parentless" alone.

**The death clause is stated at the incarnation's own kind, with no transport.**
An earlier version guarded it with `∀ sameKind : incarnation.kind = kind`, and
local adversarial review showed that guard is uninhabited at a world storing an
incarnation of the wrong kind in a slot — so a corpse satisfied the predicate.
`LogicalProcessNetworkCore.SlotsAgree` is what rules such a world out, and it is
a well-formedness clause rather than something this definition should assume;
`ProcessInstance.lifecycle` is already indexed by the incarnation's own kind, so
the clause needs no transport to be stated at all.

Note what it does *not* say: not "never had a supervisor". `.detached` also has
no current parent, and `a_corpse_may_be_orphaned` is exactly that case.
-/
def UnkilledRootAt (network : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind) : Prop :=
  ∃ incarnation, network.instances kind slot = some incarnation ∧
    incarnation.parentage.currentParent = none ∧
    ∀ reason : ProcessDeathReason, incarnation.lifecycle ≠ ProcessLifecycle.died reason

/--
**Every start has one, in the root's slot.**

`ExactInitialNetwork.rootPresent` puts an incarnation in the slot,
`rootParentage` says it is a root and `rootRunning` says it is running — the
three conjuncts in order. Nothing here is about steps.
-/
theorem start_holds_an_unkilled_root {request : (plan.topology.protocol plan.topology.root).Request}
    {network : plan.LogicalProcessNetwork} (start : plan.ExactInitialNetwork request network) :
    plan.UnkilledRootAt network plan.topology.root start.rootSlot := by
  refine ⟨start.root, start.rootPresent,
    ProcessParentage.root_currentParent start.rootParentage, ?_⟩
  intro reason dead
  rw [start.rootRunning] at dead
  cases dead

/--
**And every execution keeps one, at any plan admitting no restart at that
slot.**

`NetworkTransition.parentless_slot_survives` at every step of a run for the
parentage half, and `NetworkTransition.dying_was_supervised` for the death half.
Neither takes a well-formedness hypothesis: both are stated at the incarnation's
own kind, so no transport needs bridging and no `slotsAgree` is spent. An earlier
version carried `WellFormed` through the induction for exactly that bridge, which
was an artefact of `dying_was_supervised` having been stated at the slot's kind
rather than a fact about the invariant. The disjunct is the one
`parentless_slot_survives` concludes with:
`Restarts.restartsAChild` constrains only the new incarnation, so a restart at
the root's slot is the single way an execution can end
without a root. A plan at which that restart is unconstructible —
`ProcessGraph.maySpawn` permitting no parent for the root's role is the ordinary
reason — therefore holds a parentless undead instance in that slot along every
run, which is what `Tests/Process/PreservationFixtures.lean` discharges at
`serverPlan`. Whether that instance is the *root* is a further step: `.detached`
is parentless too, and at `serverPlan` nothing can put a detached incarnation in
the listener slot, but the predicate does not say so.

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.132. The invariant is
stated over an execution rather than over one step because a step-local fact
about the root is not what "no run reaches a dead root" needs, and local
adversarial review found exactly that gap in the first version of this argument:
each of three fixture before-worlds had been given *a* step into it while none
of them was a world of any run.
-/
theorem execution_holds_an_unkilled_root
    {kind : plan.topology.ProcessKind} {slot : plan.topology.InstanceId kind}
    {network final : plan.LogicalProcessNetwork}
    (execution : plan.StepsTo network final)
    (held : plan.UnkilledRootAt network kind slot)
    (noRestart : ∀ (before after : plan.LogicalProcessNetwork)
      (allocation : Allocation plan.topology.Carrier)
      (emitted : Trace boundary.Observation)
      (localEmitted : ObservationSegment (plan.topology.protocol kind).Observation),
      plan.Restarts before after kind slot allocation emitted localEmitted → False) :
    plan.UnkilledRootAt final kind slot := by
  induction execution with
  | still => exact held
  | more _ step carried =>
    obtain ⟨was, found, parentless, unkilled⟩ := carried
    rcases step.transition.parentless_slot_survives found parentless with
      ⟨now, foundNow, stillParentless⟩ | ⟨allocation, emitted, localEmitted, restart⟩
    · refine ⟨now, foundNow, stillParentless, ?_⟩
      intro reason dead
      exact step.transition.dying_was_supervised found unkilled foundNow dead parentless
    · exact absurd restart (noRestart _ _ allocation emitted localEmitted)

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
