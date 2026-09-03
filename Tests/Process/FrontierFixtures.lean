import Grass.Process.Network.Initial
import Grass.Process.Network.Progress

/-!
# A network that really is waiting, and the measure that says so

`docs/PROCESS.md` §7 lets an infinite network run be excused if it "remains at a
declared external frontier". `Grass/Process/Network/Progress.lean` states that as
`NetworkProgressMeasure`, and every theorem in that module is about measures.

**Nothing in this corpus had ever built one**, and three rounds of review went
into finding out why. At `serverPlan`, the M2 fixture plan, `AtFrontier` was
*empty for every measure*, because `Commits` had no provenance — a commit of an
arbitrary observation was a step of every network, and a commit is not
entropy-driven, while the field then said a frontier is left only by entropy.
`NetworkFragment.pending` fixed the commit. The next two attempts at the field
were each refuted by a fixture built against them, and the field is gone: a
frontier is a fact about which steps are enabled, `ProcessPlan.AtFrontier` is a
definition, and the per-step question is a disjunct of `descendsOrProduces`.

A measure still does not exist at `serverPlan`, and
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.67 says why: it can spawn into a fresh
connection slot from a start, so an unbounded chain of non-entropy steps is
available among *reachable* worlds, and no rank descends across it.

## What this plan is, and why it is this small

`waitingPlan` is the smallest plan at which a frontier can exist. One role, which
is the root; one slot; no channels; no shared regions; no demands, faults,
interrupt reasons or environment violations; an empty observation type; and a
protocol that never terminates.

Every one of those is load-bearing, and `entropy_or_descends` is where they are
spent — a case analysis over all twenty-four constructors of `NetworkTransition`
showing that at *any* world of this plan, a step either carries entropy or spends
one of a bounded amount of structural slack. Read it as the list of things that
have to be true before a network is *waiting* rather than merely idle.

Two of those constructors were only closed by this file's own attempts.
`childCancelled` and `childDied` did not require the instance to be a child, so
the root could be killed by a supervisor it does not have; they now carry
`wasChild`, the field `Joins` has always had.

## The one thing this fixture is careful not to claim

`waitingMeasure` chooses `Reachable := fun _ => True`, so `descendsOrProduces` is
demanded at **every** world of the plan's world type — including ones no
execution produces: an empty slot, a dead incarnation, an instance attached to a
parent that was never spawned. `slack` is the rank that pays for those, and its
whole content is that this plan's unreachable worlds admit only *finitely many*
non-entropy steps before settling into a live root.

That is a real constraint and it is not the one §7 is about. The measure could
have taken `Reachable := plan.StepsTo waiting` and said much less; it does not,
because at this plan the wider claim is affordable and the narrower one would
hide what the fixture is for. What §7 is about — an infinite run producing
nothing — this plan cannot exhibit at all, which
`waiting_is_at_a_frontier` says: every step from the start is the outside
acting.
-/

namespace Grass.Process.Tests.Frontier

open Grass.Specification
open Grass.Process

/-! ## The vocabulary: one event from outside, and nothing else -/

/-- Nothing but an external tick. Every other class is empty, which is what makes
the case analysis below finite rather than delicate. -/
@[reducible] def waitVocabulary : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := PEmpty
  InterruptReason := PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/--
A process that waits.

`TerminalResult := PEmpty` is not decoration: it is what makes
`NetworkTransition.processTermination` and `NetworkTransition.join` uninhabited,
since the first takes the result as an argument and the second requires a
terminated child. A process that can finish can be finished at any moment by a
step that is not entropy-driven.
-/
@[reducible] def waiter : ProcessSpec.{0, 0} where
  vocabulary := waitVocabulary
  Request := Unit
  State := Unit
  TerminalResult := PEmpty
  Initial := fun _ state issued emitted => state = () ∧ issued = 0 ∧ emitted = []
  Terminal := fun _ _ result => result.elim
  Step := fun _ event after issued emitted =>
    match event with
    | .external _ => after = () ∧ issued = 0 ∧ emitted = []
    | .result demand _ => demand.elim
    | .interrupted demand _ => demand.elim
    | .fault f => f.elim
    | .environmentViolation v => v.elim
  view := none

/-! ## The boundary, the registry and the graph -/

/-- The driver boundary: it may deliver a tick and nothing else, and it observes
nothing. -/
@[reducible] def waitBoundary : DriverBoundary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := PEmpty
  requirements := RequirementSet.empty

/-- The root exposes it: the tick is delivered, and there is nothing else to
export or observe. -/
@[reducible] def waitExposure : ProtocolExposesBoundary waiter waitBoundary where
  deliver := id
  exportDemand := fun demand => demand.elim
  accept := fun {demand} _ _ => demand.elim
  observe := fun observation => observation.elim

/-- The scope this fixture owns. -/
@[reducible] def waitScope : ScopeId := ⟨["Tests", "Process", "Frontier"]⟩

/-- One protocol. -/
@[reducible] def waitRegistry : ProtocolRegistry.{0, 0, 0} :=
  (⟨waitScope, Unit, fun _ => waiter⟩ : RegistryFragment.{0, 0, 0}).toRegistry

/--
One role, which is the root, and no shared state.

`maySpawn := fun _ _ => False` is what forces every incarnation this plan can
spawn or restart to be a *root*: `Spawns.authorized` and `Restarts.authorized`
demand the topology permit whatever parent the new incarnation records, so an
incarnation recording any parent at all is rejected.
-/
@[reducible] def waitGraph : ProcessGraph.{0, 0, 0, 0} waitRegistry waitBoundary where
  ProcessKind := Unit
  SharedRegion := PEmpty
  SharedState := fun region => region.elim
  protocolKey := fun _ => ()
  root := ()
  rootBoundary := waitExposure
  observeAt := fun _ observation => observation.elim
  observeAtRoot := rfl
  maySpawn := fun _ _ => False
  sharedAccess := fun _ region => region.elim
  population :=
    { bound := fun _ => .exactlyOne
      identity := fun _ => .static }

/-- One slot, and no channels. -/
@[reducible] def waitTopology : ProcessTopologyCore.{0, 0, 0, 0} waitRegistry waitBoundary where
  toProcessGraph := waitGraph
  Carrier := Unit
  carrierDecidableEq := inferInstance
  InstanceId := fun _ => Unit
  ChannelKind := PEmpty
  endpoints := fun edge => edge.elim
  spawnAuthority := fun _ _ _ _ _ => False

/-- This fixture takes no position on obligations. -/
@[reducible] def NoObligations : Type := Unit

/-- The plan. Every channel-shaped field is an elimination of the empty edge
type, which is what "no channels" costs. -/
@[reducible] def waitingPlan : ProcessPlan.{0, 0, 0, 0, 0, 0} waitRegistry waitBoundary NoObligations where
  topology := waitTopology
  message := fun edge => edge.elim
  steps := fun edge => edge.elim
  channel := fun edge => edge.elim
  sessionOpenIsRecorded := fun edge => edge.elim
  escrowImpliesOutstanding := fun edge => edge.elim

/-! ## The network that is waiting -/

/-- The root, running, holding nothing. -/
@[reducible] def theRoot : ProcessInstance waitTopology where
  kind := ()
  ref := { instanceId := (), generation := ⟨.processGeneration, ()⟩, isGeneration := rfl }
  parentage := .root
  request := ()
  localState := ()
  outstanding := 0
  lifecycle := .running

/-- The one identity this plan ever allocates: the root's generation. -/
def theRootsGeneration : Allocation waitTopology.Carrier where
  entries := [⟨.processGeneration, ()⟩]
  distinct := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem theRootsGeneration_admissible :
    (NominalHistory.initial : NominalHistory waitTopology.Carrier).Admissible
      theRootsGeneration := by
  intro nominal _ used
  exact absurd used (by simp)

/--
The history a start has: the root's generation, allocated, and nothing else.

`NominalHistory.initial` will not do, and finding that out is what
`ExactInitialNetwork.rootAllocated` is for — a start whose root carries a
generation the history has never seen is a start that fabricated an identity.
-/
def startingHistory : NominalHistory waitTopology.Carrier :=
  NominalHistory.initial.extend theRootsGeneration theRootsGeneration_admissible

/-- The network: the root is live, everything else is empty. -/
@[reducible] def waiting : waitingPlan.LogicalProcessNetwork where
  instances := fun _ _ => some theRoot
  shared := fun region => region.elim
  inFlight := fun edge => edge.elim
  sessions := fun edge => edge.elim
  obligations := ()
  observations := []
  pending := []
  usedNominals := startingHistory

theorem waiting_holds_the_root : waiting.instances () () = some theRoot := rfl

/-! ## The rank: how much structural slack a world has left -/

/--
How many non-entropy steps a world can still spend.

Not a measure of progress — this plan makes no progress, it waits — but of the
finite bookkeeping its *world type* admits before every step is a tick. A live
root is settled; a live child can be detached and then ended; an ended
incarnation can be restarted once, into a root.

The `Option`'s `none` case is an empty slot, which a spawn fills. There is no way
back: nothing here empties a slot, because `join` needs a terminated child and
`waiter.TerminalResult` is empty.
-/
def slack : Option (ProcessInstance waitTopology) → Nat
  | none => 1
  | some incarnation =>
      match incarnation.lifecycle, incarnation.parentage with
      | .running, .root => 0
      | .running, .detached _ _ => 2
      | .running, .attached _ _ => 4
      | _, .root => 1
      | _, .detached _ _ => 1
      | _, .attached _ _ => 2

/-- The rank of a world is the slack of its one slot. -/
def rankOf (network : waitingPlan.LogicalProcessNetwork) : Nat :=
  slack (network.instances () ())

theorem rankOf_waiting : rankOf waiting = 0 := rfl

/-! ## Two facts about what this plan may install -/

/--
**Anything spawned or restarted here is a root.**

`Spawns.authorized` and `Restarts.authorized` both say the topology must permit
whatever parent the new incarnation records, and `maySpawn` permits none — so the
only incarnation either may install is one recording no parent at all.
-/
theorem authorized_is_root {incarnation : ProcessInstance waitTopology}
    (authorized : ∀ parentKind parent,
      incarnation.parentage.knownParent = some ⟨parentKind, parent⟩ →
        waitTopology.maySpawn parentKind incarnation.kind) :
    incarnation.parentage = .root := by
  cases parentage : incarnation.parentage with
  | root => rfl
  | attached parentKind parent =>
    exact absurd (authorized parentKind parent (by rw [parentage]; rfl)) (fun h => h)
  | detached parentKind parent =>
    exact absurd (authorized parentKind parent (by rw [parentage]; rfl)) (fun h => h)

/-- So its slack is zero if it is live. -/
theorem slack_of_live_root {incarnation : ProcessInstance waitTopology}
    (live : incarnation.Live) (isRoot : incarnation.parentage = .root) :
    slack (some incarnation) = 0 := by
  have running : incarnation.lifecycle = .running :=
    ProcessLifecycle.live_iff_running.mp live
  simp only [slack, running, isRoot]


/-- A dead incarnation still has slack: it can be restarted, once. -/
theorem slack_of_dead {incarnation : ProcessInstance waitTopology}
    (dead : ¬ incarnation.Live) : 1 ≤ slack (some incarnation) := by
  have notRunning : incarnation.lifecycle ≠ .running :=
    fun running => dead (ProcessLifecycle.live_iff_running.mpr running)
  cases lifecycle : incarnation.lifecycle with
  | running => exact absurd lifecycle notRunning
  | _ =>
    cases parentage : incarnation.parentage <;>
      simp only [slack, lifecycle, parentage] <;> omega

/-- Detaching spends slack, whether the child is alive or not. -/
theorem slack_detach {before after : ProcessInstance waitTopology}
    (attached : ∃ parentKind parent, before.parentage = .attached parentKind parent)
    (sameLifecycle : after.lifecycle = before.lifecycle)
    (detached : ∃ parentKind parent, after.parentage = .detached parentKind parent) :
    slack (some after) < slack (some before) := by
  obtain ⟨_, _, isAttached⟩ := attached
  obtain ⟨_, _, isDetached⟩ := detached
  cases lifecycle : before.lifecycle <;>
    simp only [slack, isAttached, isDetached, sameLifecycle, lifecycle] <;> omega

/-- And ending a child spends slack, whichever kind of child it is. -/
theorem slack_end {before after : ProcessInstance waitTopology}
    (live : before.Live) (dead : ¬ after.Live)
    (sameParentage : after.parentage = before.parentage)
    (hasParent : before.parentage.currentParent ≠ none) :
    slack (some after) < slack (some before) := by
  have running : before.lifecycle = .running := ProcessLifecycle.live_iff_running.mp live
  have notRunning : after.lifecycle ≠ .running :=
    fun isRunning => dead (ProcessLifecycle.live_iff_running.mpr isRunning)
  cases parentage : before.parentage with
  | root => exact absurd (parentage ▸ rfl : before.parentage.currentParent = none) hasParent
  | detached _ _ =>
    exact absurd (parentage ▸ rfl : before.parentage.currentParent = none) hasParent
  | attached _ _ =>
    cases lifecycle : after.lifecycle <;>
      simp only [slack, running, parentage, sameParentage, lifecycle] <;>
      first
        | omega
        | exact absurd lifecycle notRunning

/--
Ending a child spends slack.

The shared body of `childCancelled` and `childDied`: both carry an
`EndsInstance` and a `wasChild`, and the two together say the incarnation was
live, is not, kept its parentage, and was not the root.
-/
theorem ends_a_child {before after : waitingPlan.LogicalProcessNetwork}
    {ending : ProcessLifecycle (waitTopology.protocol ())}
    {custody : Bag (waitTopology.protocol ()).Demand → NoObligations → NoObligations → Prop}
    (wasChild : ∀ incarnation, before.instances () () = some incarnation →
      incarnation.parentage.currentParent ≠ none)
    (step : waitingPlan.EndsInstance before after () () ending custody) :
    rankOf after < rankOf before := by
  obtain ⟨was, foundWas, live⟩ := step.wasLive
  obtain ⟨ended, foundEnded, _, isEnding⟩ := step.nowEnded
  obtain ⟨fromInstance, toInstance, _, _, foundBefore, foundAfter,
    _, sameParentage, _⟩ := step.identityPreserved
  have sameWas : was = fromInstance := Option.some.inj (foundWas ▸ foundBefore)
  have sameEnded : ended = toInstance := Option.some.inj (foundEnded ▸ foundAfter)
  have liveBefore : fromInstance.Live := sameWas ▸ live
  have endingAfter : toInstance.lifecycle = ending := by
    have stated : ended.lifecycle = ending := isEnding
    exact sameEnded ▸ stated
  have sameParentage' : toInstance.parentage = fromInstance.parentage := sameParentage
  have notLive : ¬ toInstance.Live := by
    intro isLive
    exact step.notRunning (endingAfter ▸ ProcessLifecycle.live_iff_running.mp isLive)
  show slack (after.instances () ()) < slack (before.instances () ())
  rw [foundBefore, foundAfter]
  exact slack_end liveBefore notLive sameParentage' (wasChild fromInstance foundBefore)

/-! ## Every step is entropy, or spends slack -/

/--
**At any world of this plan, a step carries entropy or the rank descends.**

`NetworkProgressMeasure.descendsOrProduces` for this plan, and the list of what
has to be true before a network is *waiting* rather than merely idle. Eighteen of
the twenty-four constructors are uninhabited here and the reasons are worth
reading as a group:

* `interrupt`, `fault` and `environmentViolation` take a reason from the
  protocol's vocabulary, and all three classes are empty.
* `processTermination` takes a `TerminalResult`, and `join` a terminated child;
  the result type is empty.
* the twelve channel constructors take a `ChannelKind`, which is empty.
* `commit` needs a non-empty trace of an empty observation type. (Its
  `Commits.earned` would also need `pending` non-empty, which is a second,
  independent reason.)

Of the six that remain, `processStep` is the frontier's exit — `waiter.Step`
admits only `.external`, so the event carries entropy. `spawn`, `restart`,
`detach` and the two child endings each spend slack, which is what §7's own
progress list ("process steps, spawn, retry, cancellation, death, join, and
restart") asks of them. Two of those six are inhabited at this plan and a
reviewer built them; `timeout` is closed by being entropy rather than by its edge
type being empty, which is a seventh reason and not one of the eighteen.

`childCancelled` and `childDied` did not require the instance to be a child
until this theorem was attempted. Without that, a root could be killed by a
supervisor it does not have — and then no world of any plan is ever waiting,
because every live network can be ended by a step that is not entropy-driven.
-/
theorem entropy_or_descends {before after : waitingPlan.LogicalProcessNetwork}
    (transition : waitingPlan.NetworkTransition before after) :
    transition.DrivenByEntropy ∨ rankOf after < rankOf before := by
  cases transition with
  | processStep kind slot event _ _ _ step =>
    refine Or.inl ?_
    match event, step.protocolStep with
    | .external _, _ => trivial
    | .result demand _, _ => exact demand.elim
    | .interrupted demand _, _ => exact demand.elim
    | .fault f, _ => exact f.elim
    | .environmentViolation v, _ => exact v.elim
  | spawn kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨fresh, found, _, _⟩ := step.nowLive
    exact absurd
      ((authorized_is_root (step.authorized fresh found)) ▸ rfl :
        fresh.parentage.currentParent = none)
      (step.spawnsAChild fresh found)
  | restart kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨old, foundOld, dead⟩ := step.wasEnded
    obtain ⟨fresh, found, live, _⟩ := step.nowLive
    refine Or.inr ?_
    show slack (after.instances () ()) < slack (before.instances () ())
    rw [foundOld, found]
    rw [slack_of_live_root live (authorized_is_root (step.authorized fresh found))]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (slack_of_dead dead)
  | detach kind slot step =>
    cases kind; cases slot
    obtain ⟨was, foundWas, hadParent⟩ := step.wasAttached
    obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
      isDetach, sameLifecycle, _⟩ := step.identityPreserved
    cases fromKind; cases toKind
    have same : was = fromInstance := Option.some.inj (foundWas ▸ foundBefore)
    subst same
    refine Or.inr ?_
    show slack (after.instances () ()) < slack (before.instances () ())
    rw [foundBefore, foundAfter]
    refine slack_detach ?_ sameLifecycle ?_
    · cases parentage : was.parentage with
      | root => exact absurd (parentage ▸ rfl : was.parentage.currentParent = none) hadParent
      | attached parentKind parent => exact ⟨parentKind, parent, rfl⟩
      | detached _ _ =>
        exact absurd (parentage ▸ rfl : was.parentage.currentParent = none) hadParent
    · cases parentage : was.parentage with
      | root => exact absurd (parentage ▸ rfl : was.parentage.currentParent = none) hadParent
      | attached parentKind parent =>
        have isDetach' : toInstance.parentage = was.parentage.detach := isDetach
        exact ⟨parentKind, parent, by rw [isDetach', parentage]; rfl⟩
      | detached parentKind parent =>
        have isDetach' : toInstance.parentage = was.parentage.detach := isDetach
        exact ⟨parentKind, parent, by rw [isDetach', parentage]; rfl⟩
  | childCancelled kind slot _ _ wasChild step =>
    cases kind; cases slot
    exact Or.inr (ends_a_child wasChild step)
  | childDied kind slot _ _ wasChild step =>
    cases kind; cases slot
    exact Or.inr (ends_a_child wasChild step)
  | interrupt _ _ reason _ _ => exact reason.elim
  | fault _ _ f _ _ => exact f.elim
  | environmentViolation _ _ violation _ _ => exact violation.elim
  | processTermination _ _ result _ _ => exact result.elim
  | join _ _ result _ => exact result.elim
  | commit emitted step =>
    exact absurd (match emitted with
      | [] => rfl
      | observation :: _ => observation.elim) step.nonempty
  | send edge _ _ _ => exact edge.elim
  | receive edge _ _ _ => exact edge.elim
  | requestCancel edge _ _ _ => exact edge.elim
  | acknowledgeCancel edge _ _ _ => exact edge.elim
  | timeout _ _ _ _ => exact Or.inl trivial
  | senderDeath edge _ _ _ _ => exact edge.elim
  | receiverDeath edge _ _ _ _ => exact edge.elim
  | drop edge _ _ _ => exact edge.elim
  | coalesce edge _ _ _ _ => exact edge.elim
  | reroute edge _ _ _ _ => exact edge.elim
  | channelClose edge _ _ _ => exact edge.elim
  | channelDeath edge _ _ _ => exact edge.elim

/--
**And at `waiting` itself, only entropy moves it at all.**

The strong statement `entropy_or_descends` had to weaken in order to cover every
world of the plan, including the ones no run reaches. At `waiting` the slack is
already zero, so no step can descend and the disjunction collapses.

This is `ProcessPlan.AtFrontier waiting` — §7's "declared external frontier",
which is a definition about which steps are enabled rather than anything a
measure says.
-/
theorem only_entropy_moves_it {after : waitingPlan.LogicalProcessNetwork}
    (transition : waitingPlan.NetworkTransition waiting after) :
    transition.DrivenByEntropy :=
  (entropy_or_descends transition).elim id
    (fun descends => absurd descends (by rw [rankOf_waiting]; exact Nat.not_lt_zero _))


/-! ## And it is where a run begins -/

/--
**`waiting` is an exact initial network.**

The record `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.59 recorded as having no
witness, and §10.65 as being disconnected from the measure. This closes the first
and half of the second: `waitingMeasure` is indexed by `waiting`, and `waiting`
is a network a run may begin at.

Sixteen fields, and **one** of them took work. `rootAllocated` is law 22: the
root's generation has to be in the nominal history, so the history a run starts
from is not `NominalHistory.initial` but that history extended once, which this
fixture was quietly getting wrong.

The rest are discharged by the shape of the plan rather than by anything about
`waiting`, and a reviewer checked how many: `nothingCommitted` and
`pendingProjected` cannot fail here at all, because `waitBoundary.Observation` is
empty and so every world of this plan has both traces empty; `onlyTheRoot` is
`fun _ _ _ _ => ⟨rfl, rfl⟩` because kind and slot are `Unit`; `nothingInFlight`
and `sessionsFresh` are eliminations of the empty edge type. At most five of the
sixteen carry content at this plan.

That is worth saying rather than leaving for the next reader to find. The record
is *inhabited* — which it was not, and which is what
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.59 asked for — and it is not
*exercised*. A fixture that exercises it needs a plan with channels, several
roles and an inhabited observation type, and that plan is the one §10.67 says has
no measure.
-/
def waiting_is_a_start : waitingPlan.ExactInitialNetwork () waiting where
  rootSlot := ()
  root := theRoot
  rootPresent := rfl
  rootKind := rfl
  rootSlotAgrees := rfl
  rootEmitted := []
  rootInitial := ⟨rfl, rfl, rfl⟩
  pendingProjected := rfl
  nothingCommitted := rfl
  rootRequest := rfl
  rootRunning := rfl
  rootParentage := trivial
  rootAllocated := by simp [ProcessTopologyCore.ProcessRef.Allocated, startingHistory,
    theRootsGeneration, NominalHistory.extend]
  onlyTheRoot := fun _ _ _ _ => ⟨rfl, rfl⟩
  nothingInFlight := fun edge => edge.elim
  sessionsFresh := fun edge => edge.elim
  historyFromEmpty := .extend (.refl _) theRootsGeneration theRootsGeneration_admissible


/-! ## An empty slot nothing can fill, and a child the program lets go -/

/--
The same plan with nobody in the slot, and no history.

Not a start — `ExactInitialNetwork.rootPresent` needs an incarnation — and, since
`Spawns` gained `spawnsAChild`, not a network any step can leave: a spawn needs a
parent and there is nobody to be one, a restart needs an ended incarnation and
the slot is empty, and every other constructor is uninhabited at this plan.

`nothing_moves_the_empty_world` is that, and it is worth having because
`ProcessPlan.AtFrontier` holds of it *vacuously*. "Only the outside can move this
network" is satisfied by a network nothing can move at all, so a frontier and a
deadlock are indistinguishable at this definition.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.71 records it.
-/
@[reducible] def emptyWorld : waitingPlan.LogicalProcessNetwork :=
  { waiting with
      instances := fun _ _ => none
      usedNominals := NominalHistory.initial }

/-- A network holding one given incarnation in the one slot. -/
@[reducible] def holdingOne
    (incarnation : ProcessInstance waitTopology) : waitingPlan.LogicalProcessNetwork :=
  { waiting with instances := fun _ _ => some incarnation }

/-- Only that slot differs between two of them. -/
theorem holdingOne_changesOne (left right : ProcessInstance waitTopology) :
    waitingPlan.ChangesOneInstance (holdingOne left) (holdingOne right) () () where
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind slot =>
      cases kind; cases slot
      exact absurd rfl outside
    | region region => exact region.elim
    | escrow edge _ => exact edge.elim
    | session edge _ => exact edge.elim
    | _ => rfl

/-- A live child of the root: not a shape a run of this plan reaches, since
nothing may spawn here, but a world of its world type. -/
@[reducible] def attachedChild : ProcessInstance waitTopology :=
  { theRoot with parentage := .attached () theRoot.ref }

/-- The same child, let go. -/
@[reducible] def detachedChild : ProcessInstance waitTopology :=
  { attachedChild with parentage := attachedChild.parentage.detach }

/--
**Detaching it is a step of this plan.**

The non-entropy step the fixture needs, and it replaces a spawn that should never
have been one: `the_spawn` used to install the *root*, modelling a program's
start as a transition. `Spawns.spawnsAChild` now forbids that, and finding it is
what the attempt at a well-formedness capstone produced.
-/
theorem the_detach :
    waitingPlan.Detaches (holdingOne attachedChild) (holdingOne detachedChild) () () where
  wasAttached := ⟨attachedChild, rfl, by intro equal; cases equal⟩
  identityPreserved :=
    ⟨attachedChild, detachedChild, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  onlyThatSlot := holdingOne_changesOne attachedChild detachedChild

/-- As a step: a detach allocates nothing, so the history does not move. -/
def detachStep : waitingPlan.NetworkStep (holdingOne attachedChild) (holdingOne detachedChild) where
  transition := .detach () () the_detach
  admissible := by
    intro nominal allocated
    exact absurd allocated (fun inEmpty => List.not_mem_nil inEmpty)
  historyExact := (NominalHistory.extend_empty _ _).symm

/-- **It is not entropy**: the parent let go on its own initiative. -/
theorem the_detach_is_not_entropy : ¬ detachStep.transition.DrivenByEntropy := id

/--
**Nothing at all moves the empty world.**

Every constructor needs something this network does not have: `processStep` a
live incarnation, `spawn` a parent, `restart` an ended one, `detach` an attached
one, the endings a live one, `join` a terminated one, `commit` a non-empty trace
of an empty observation type, and the twelve channel constructors an edge.

`ProcessPlan.AtFrontier emptyWorld` therefore holds — vacuously. §7's frontier is
"only the outside can move this network", and a network nothing can move at all
satisfies it. So a frontier and a deadlock are indistinguishable at this
definition, and §7's progress theorem excuses both.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.71.
-/
theorem nothing_moves_the_empty_world {after : waitingPlan.LogicalProcessNetwork}
    (transition : waitingPlan.NetworkTransition emptyWorld after) : False := by
  cases transition with
  | processStep kind slot _ _ _ _ step =>
    cases kind; cases slot
    obtain ⟨_, found, _, _⟩ := step.from'
    exact absurd found (by simp)
  | spawn kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨fresh, found, _, _⟩ := step.nowLive
    exact absurd
      ((authorized_is_root (step.authorized fresh found)) ▸ rfl :
        fresh.parentage.currentParent = none)
      (step.spawnsAChild fresh found)
  | restart kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨_, found, _⟩ := step.wasEnded
    exact absurd found (by simp)
  | detach kind slot step =>
    cases kind; cases slot
    obtain ⟨_, found, _⟩ := step.wasAttached
    exact absurd found (by simp)
  | childCancelled kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨_, found, _⟩ := step.wasLive
    exact absurd found (by simp)
  | childDied kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨_, found, _⟩ := step.wasLive
    exact absurd found (by simp)
  | join kind slot result _ => exact result.elim
  | interrupt _ _ reason _ _ => exact reason.elim
  | fault _ _ f _ _ => exact f.elim
  | environmentViolation _ _ violation _ _ => exact violation.elim
  | processTermination _ _ result _ _ => exact result.elim
  | commit emitted step =>
    exact step.nonempty (match emitted with
      | [] => rfl
      | observation :: _ => observation.elim)
  | send edge _ _ _ => exact edge.elim
  | receive edge _ _ _ => exact edge.elim
  | requestCancel edge _ _ _ => exact edge.elim
  | acknowledgeCancel edge _ _ _ => exact edge.elim
  | timeout edge _ _ _ => exact edge.elim
  | senderDeath edge _ _ _ _ => exact edge.elim
  | receiverDeath edge _ _ _ _ => exact edge.elim
  | drop edge _ _ _ => exact edge.elim
  | coalesce edge _ _ _ _ => exact edge.elim
  | reroute edge _ _ _ _ => exact edge.elim
  | channelClose edge _ _ _ => exact edge.elim
  | channelDeath edge _ _ _ => exact edge.elim

/-- **So it is at a frontier**, which is exactly the problem. -/
theorem the_empty_world_is_a_frontier : waitingPlan.AtFrontier emptyWorld :=
  fun step => (nothing_moves_the_empty_world step.transition).elim

/-! ## So a measure exists, and it is a useful one -/

/--
**Entropy needs somebody to deliver it to.**

The half of the frontier argument that is about the world rather than about the
vocabulary: only a `processStep` can be entropy-driven here — `timeout` takes a
channel edge and there are none — and a `processStep` needs a live incarnation to
step. So a network with an empty slot cannot be moved from outside at all.
-/
theorem entropy_needs_a_live_instance {before after : waitingPlan.LogicalProcessNetwork}
    (transition : waitingPlan.NetworkTransition before after)
    (entropy : transition.DrivenByEntropy) :
    ∃ incarnation, before.instances () () = some incarnation ∧ incarnation.Live := by
  cases transition with
  | processStep kind slot _ _ _ _ step =>
    cases kind; cases slot
    obtain ⟨incarnation, found, live, _⟩ := step.from'
    exact ⟨incarnation, found, live⟩
  | timeout edge _ _ _ => exact edge.elim
  | _ => exact absurd entropy (fun h => h)

/--
**A `NetworkProgressMeasure` for `waitingPlan`.**

The positive witness `Grass/Process/Network/Progress.lean` did not have. Every
theorem in that module quantifies over measures, and until this definition
existed none of them was known to be about anything — and at the M2 plan a
reviewer proved they were about nothing at all.

`descendsOrProduces` is discharged straight from `entropy_or_descends`, and that
is the whole of the measure's content: every step of this plan is either the
outside acting or spends a bounded amount of structural slack.

Two earlier versions of this definition had an `AtFrontier` field, and reviewers
refuted both. The first set it to `fun _ => True` and argued that "at this plan
every network *is* waiting"; `emptyWorld` refutes that, since no step out of it is
entropy-driven and the program leaves it by spawning. The second set it to "the
slot holds a live incarnation", and a live *attached* child refutes that, since
the program detaches on its own initiative. The field is gone —
`ProcessPlan.AtFrontier` is a definition about which steps are enabled, and a
measure cannot get it wrong because a measure no longer says.

`Reachable := fun _ => True` is the *widest* choice, and therefore the hardest:
the obligation is demanded at every world, including the ones no run reaches.
`slack` is what pays for those, and `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.64
is why a plan that does interesting work cannot.
-/
def waitingMeasure : waitingPlan.NetworkProgressMeasure waiting where
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  rankTransitive := fun _ _ _ below above => Nat.lt_trans below above
  rank := rankOf
  demanded := fun observation => observation.elim
  Reachable := fun _ => True
  startIsInitial := ⟨(), ⟨waiting_is_a_start⟩⟩
  reachableStart := trivial
  reachableClosed := fun _ _ => trivial
  descendsOrProduces := fun _ step =>
    (entropy_or_descends step.transition).elim Or.inl (fun descends => Or.inr (Or.inl descends))

/--
**`emptyWorld` is not at a frontier**, so this plan is `Useful`: it has a network
the program itself can move.

`AtFrontier` and `Useful` are facts about the plan now rather than declarations a
measure makes, so this holds whatever measure anyone writes. That is the point of
the change — two rounds were spent on measures declaring the wrong networks
paused.
-/
theorem the_plan_is_useful : waitingPlan.Useful :=
  ⟨holdingOne attachedChild, fun paused => the_detach_is_not_entropy (paused detachStep)⟩

/--
**The detach is a silent run**, so this plan's `SilentRun` class is not empty.

That matters more than it looks. `SilentRun` used to require each step to start
at a network the *measure* did not call paused, so under an all-paused measure the
class was empty and every theorem in `Grass/Process/Network/Progress.lean` —
including its headline `no_infinite_silent_run` — was discharged from its own
hypothesis at the corpus's only measure. A reviewer proved that. It now requires
the step itself not to be entropy-driven, which nothing can declare away, and a
detach is such a step.
-/
theorem the_detach_is_a_silent_run :
    ProcessPlan.NetworkProgressMeasure.SilentRun waitingMeasure
      (holdingOne attachedChild) (holdingOne detachedChild) :=
  .one detachStep trivial
    (fun _ observation _ _ _ => observation.elim)
    the_detach_is_not_entropy

/-- **So the measure pays for it**, which is `silent_run_descends` at a run that
exists: `slack` falls from 4 to 2, because a detached child has one fewer thing
that can happen to it than an attached one. -/
theorem the_detach_costs_rank :
    waitingMeasure.rankLt (waitingMeasure.rank (holdingOne detachedChild))
      (waitingMeasure.rank (holdingOne attachedChild)) :=
  waitingMeasure.silent_run_descends the_detach_is_a_silent_run


/-! ## And the network really does run forever at it -/

/--
**A tick is a step of this plan, from `waiting` back to `waiting`.**

The frontier is not a state the network is stuck in for want of a transition: it
has one, and taking it returns the identical world. That is the shape §7 excuses
— "an infinite network run must produce a specification-demanded observation **or
remain at a declared external frontier**" — and it is the shape
`Grass/Process/Network/Progress.lean`'s `SilentRun` is careful to exclude by
requiring each of its steps to start off-frontier.
-/
theorem the_tick_is_a_step : waitingPlan.StepsLocally waiting waiting () () (.external ()) [] 0 [] where
  from' := ⟨theRoot, rfl, trivial, rfl⟩
  stillLive := ⟨theRoot, rfl, trivial⟩
  protocolStep := ⟨theRoot, theRoot, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, (by show (0 : Bag waitVocabulary.Demand) = 0 + 0; simp), rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := rfl
  writesPermitted := fun region _ => region.elim
  scope := by
    intro fragment _
    cases fragment with
    | region region => exact region.elim
    | escrow edge _ => exact edge.elim
    | session edge _ => exact edge.elim
    | _ => rfl

/-- As a transition, and as a step: nothing is allocated, so the freshness law
is the empty one. -/
def tickStep : waitingPlan.NetworkStep waiting waiting where
  transition := .processStep () () (.external ()) [] 0 [] the_tick_is_a_step
  admissible := by
    intro nominal allocated
    exact absurd allocated (fun inEmpty => List.not_mem_nil inEmpty)
  historyExact := (NominalHistory.extend_empty _ _).symm

/-- **It is driven by entropy**, so the frontier does not have to pay for it. -/
theorem the_tick_is_entropy : tickStep.transition.DrivenByEntropy := trivial

/-- **And the world it reaches is the world it left.** -/
theorem the_tick_returns_to_waiting :
    ∃ _ : waitingPlan.NetworkStep waiting waiting, True := ⟨tickStep, trivial⟩


/--
**So the measure's index is a start, not an arbitrary world.**

`NetworkProgressMeasure.startIsInitial` is the field that says so, and it could
not be stated until this record had a witness: a field demanding an uninhabited
record makes the record demanding it uninhabited too. So the order was
`waiting_is_a_start` first, then the field, then this — which is why §10.59 had
to close before §10.65 could.
-/
theorem the_measure_starts_where_a_run_starts :
    Nonempty (waitingPlan.ExactInitialNetwork () waiting) ∧ waitingMeasure.Reachable waiting :=
  ⟨⟨waiting_is_a_start⟩, waitingMeasure.reachableStart⟩



/--
**And `waiting` really is a frontier**: the outside is the only thing that can
move it.

Not a claim any measure makes — `ProcessPlan.AtFrontier` is a definition, so this
is a fact about the plan.

The consequence worth stating with it: no `SilentRun` begins at `waiting`, under
any measure, because a silent run's first step is not entropy-driven and every
step from `waiting` is. That is not a defect — it is what "this network is
waiting" means — and it is why the silent-run class needed `emptyWorld` to be
non-empty.
-/
theorem waiting_is_at_a_frontier : waitingPlan.AtFrontier waiting :=
  fun step => only_entropy_moves_it step.transition


/-! ## And it is well formed -/

/--
**`waiting` is a well-formed network.**

`LogicalProcessNetworkCore.WellFormed` and `ProcessPlan.Sound` were inhabited
nowhere in the corpus — `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.79 — so
`ProcessPlan.terminated_result_is_exact` took a hypothesis nothing had ever
supplied. This is the first witness.

Five of its six clauses are discharged by the shape of this plan rather than by
anything about `waiting`: kind and slot are `Unit`, the root has no parent, the
protocol has no terminal result, and there are no channels. `nominalsAllocated`
is the one with content, and it is the same fact `waiting_is_a_start`'s
`rootAllocated` needed: the root's generation is in the history because the
history is `NominalHistory.initial` extended by exactly it.

That is worth saying rather than leaving to be found. A record inhabited only
where five of six clauses cannot fail is inhabited and not exercised, which is
the distinction §10.59 drew for `ExactInitialNetwork` at this same plan.
-/
theorem waiting_is_wellFormed : waiting.WellFormed where
  slotsAgree := fun _ _ incarnation found => by
    injection found with same
    subst same
    exact ⟨rfl, rfl⟩
  lifecyclesWitnessed := fun _ _ incarnation found => by
    injection found with same
    subst same
    intro result _
    exact result.elim
  rootUnique := fun _ _ _ _ _ _ _ _ => rfl
  parentageValid := fun _ _ incarnation found _ _ known => by
    injection found with same
    subst same
    exact absurd known (by simp [ProcessParentage.knownParent])
  nominalsAllocated := fun _ _ incarnation found => by
    injection found with same
    subst same
    simp [ProcessTopologyCore.ProcessRef.Allocated, startingHistory,
      theRootsGeneration, NominalHistory.extend]
  reroutesLand := fun edge => edge.elim
  occurrencesOnTheirSession := fun edge _ _ _ => edge.elim

/-- **So it is sound**, which is what `terminated_result_is_exact` wanted. -/
theorem waiting_is_sound : waitingPlan.Sound waiting :=
  ⟨waiting_is_wellFormed⟩


end Grass.Process.Tests.Frontier
