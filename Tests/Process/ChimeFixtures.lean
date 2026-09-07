import Grass.Process.Network.Progress
import Grass.Process.Network.Initial

/-!
# The plan whose progress is a production, not a descent

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.88. `NetworkProgressMeasure` has had
one witness family in this corpus, `Tests/Process/FrontierFixtures.lean`'s
`waitingMeasure`, at a plan whose `Observation` type is `PEmpty`. Its `demanded`
is therefore `observation.elim`, and its `descendsOrProduces` is
`entropy_or_descends`: every step is entropy or descends the rank.

So **§7's third escape has never been able to fire anywhere**. The clause reads

> an infinite network run must produce a specification-demanded observation **or**
> remain at a declared external frontier

and the corpus has only ever exhibited the second half. A disjunct that no plan
can reach is the same shape as a record nothing inhabits, and this milestone has
spent eight review rounds on that class of defect.

This plan reaches the first half. It is the `waitingPlan` skeleton — one role,
one slot, no channels, nothing spawnable — with two changes: the observation type
is inhabited, and the root *starts* holding one observation it has already
produced. `chiming_is_a_start` is the `ExactInitialNetwork`, whose
`pendingProjected` puts that observation in the network's pending trace, and
`the_chime_is_committed` publishes it.

## What can happen here

`commit` is the only step this plan admits at `chiming` and at `chimed`, and the
reasons are worth listing, because the argument is the fixture:

* every channel constructor needs a `ChannelKind`, and there is none;
* `processStep` needs `ProcessSpec.Step`, which is `False` here — so unlike
  `waitingPlan`, whose frontier is left by an external event, this plan has no
  entropy-driven step at all;
* `spawn` and `restart` install an incarnation whose parent the topology permits,
  and `maySpawn` permits none, while `Spawns.spawnsAChild` and
  `Restarts.restartsAChild` demand a parent;
* `interrupt`, `fault` and `environmentViolation` need an inhabited reason class,
  and all three are `PEmpty`;
* `processTermination` and `join` need a `TerminalResult`, which is `PEmpty`;
* `detach`, `childCancelled` and `childDied` need the instance to have a current
  parent, and the only instance either network holds is the root.

The last line is about *these two networks*, not about the plan.
`LogicalProcessNetwork` is a record, so its unreachable inhabitants include a
world whose slot holds an attached child, and at such a world a detach or a child
ending is a perfectly good step that publishes nothing. A measure whose
`Reachable` is `fun _ => True` owes `descendsOrProduces` there too. So the rank
below is `Tests/Process/FrontierFixtures.lean`'s structural slack, unchanged:
those three steps spend it, and the commit — which does not touch `instances` at
all — leaves it exactly where it was and pays with the observation instead.

## What this does and does not show

It shows §7's production disjunct is reachable, which is what §10.88 asked for,
and `the_chime_takes_the_production_disjunct` shows it is *taken*: at the chime
step the other two disjuncts are both false. `produces_or_descends` also makes
this the corpus's first measure that both descends and produces, rather than one
that only ever descends.

It does not show an infinite producing run, and this plan cannot: the root's
initial segment is finite, `Commits.earned` publishes each observation once, and
after the commit `pending` is empty, so no second commit is possible.
`nothing_happens_after_the_chime` states that plainly rather than leaving a
reader to infer it.
-/

namespace Grass.Process.Tests.Chime

open Grass.Specification
open Grass.Process

/-! ## A vocabulary with something to say -/

/-- The one thing this process ever observes. -/
inductive Chime
  | chime
  deriving DecidableEq, Repr

/--
One external event and one observation. Every exceptional class stays empty, for
the reason `Tests/Process/FrontierFixtures.lean` gives: it is what keeps the
case analysis over the transition family finite.
-/
@[reducible] def chimeVocabulary : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := Chime
  InterruptReason := fun _ => PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/--
A process that has already spoken and will never step again.

`Step := fun _ _ _ _ _ => False` is the field doing the work. It makes
`NetworkTransition.processStep` uninhabited, which leaves `commit` as the only
constructor this plan admits — see the module note. `TerminalResult := PEmpty`
does the same job for `processTermination` and `join` that it does at
`waitingPlan`.
-/
@[reducible] def chimer : ProcessSpec.{0, 0} where
  vocabulary := chimeVocabulary
  Request := Unit
  State := Unit
  TerminalResult := PEmpty
  Initial := fun _ state issued emitted =>
    state = () ∧ issued = 0 ∧ emitted = [Chime.chime]
  Terminal := fun _ _ result => result.elim
  Step := fun _ _ _ _ _ => False
  view := none

/-! ## The boundary, registry and graph -/

/-- The driver may deliver a tick, and it observes chimes. -/
@[reducible] def chimeBoundary : DriverBoundary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := Chime
  requirements := RequirementSet.empty

/-- The root exports its observation unchanged, which is what lets a chime the
process produced reach the network's trace at all. -/
@[reducible] def chimeExposure : ProtocolExposesBoundary chimer chimeBoundary where
  deliver := id
  exportDemand := fun demand => demand.elim
  accept := fun {demand} _ _ => demand.elim
  observe := some

/-- The scope this fixture owns. -/
@[reducible] def chimeScope : ScopeId := ⟨["Tests", "Process", "Chime"]⟩

/-- One protocol. -/
@[reducible] def chimeRegistry : ProtocolRegistry.{0, 0, 0} :=
  (⟨chimeScope, Unit, fun _ => chimer⟩ : RegistryFragment.{0, 0, 0}).toRegistry

/-- One role, which is the root, and nothing it may spawn. -/
@[reducible] def chimeGraph : ProcessGraph.{0, 0, 0, 0} chimeRegistry chimeBoundary where
  ProcessKind := Unit
  SharedRegion := PEmpty
  SharedState := fun region => region.elim
  protocolKey := fun _ => ()
  root := ()
  rootBoundary := chimeExposure
  observeAt := fun _ observation => some observation
  observeAtRoot := rfl
  maySpawn := fun _ _ => False
  sharedAccess := fun _ region => region.elim
  sharedInvariant := fun region => region.elim
  population :=
    { bound := fun _ => .exactlyOne
      identity := fun _ => .static }

/-- One slot, and no channels. -/
@[reducible] def chimeTopology : ProcessTopologyCore.{0, 0, 0, 0} chimeRegistry chimeBoundary where
  toProcessGraph := chimeGraph
  Carrier := Unit
  carrierDecidableEq := inferInstance
  InstanceId := fun _ => Unit
  ChannelKind := PEmpty
  endpoints := fun edge => edge.elim
  spawnAuthority := fun _ _ _ _ _ => False

/-- This fixture takes no position on obligations. -/
@[reducible] def NoObligations : Type := Unit

/-- The plan. -/
@[reducible] def chimingPlan :
    ProcessPlan.{0, 0, 0, 0, 0, 0} chimeRegistry chimeBoundary NoObligations where
  topology := chimeTopology
  message := fun edge => edge.elim
  steps := fun edge => edge.elim
  channel := fun edge => edge.elim
  sessionOpenIsRecorded := fun edge => edge.elim
  -- No channels, so nothing can coalesce and no shared regions, so nothing can
  -- be written: `ProcessPlan.coalescing`, `sharedUpdate` and their laws are all
  -- eliminations here. Both notes say the cost lands only on plans that use the
  -- feature; this is what that looks like.
  coalescing := fun edge => edge.elim
  sharedUpdate := fun _ _ _ _ _ _ region => region.elim
  sharedUpdatePreserves := fun _ _ _ _ _ _ region => region.elim
  escrowImpliesOutstanding := fun edge => edge.elim

/-! ## The network that has something to publish -/

/-- The root, running, holding nothing outstanding. -/
@[reducible] def theRoot : ProcessInstance chimeTopology where
  kind := ()
  ref := { instanceId := (), generation := ⟨.processGeneration, ()⟩, isGeneration := rfl }
  parentage := .root
  request := ()
  localState := ()
  outstanding := 0
  lifecycle := .running

/-- The one identity this plan allocates. -/
def theRootsGeneration : Allocation chimeTopology.Carrier where
  entries := [⟨.processGeneration, ()⟩]
  distinct := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem theRootsGeneration_admissible :
    (NominalHistory.initial : NominalHistory chimeTopology.Carrier).Admissible
      theRootsGeneration := by
  intro nominal _ used
  exact absurd used (by simp)

/-- The history a start has. -/
def startingHistory : NominalHistory chimeTopology.Carrier :=
  NominalHistory.initial.extend theRootsGeneration theRootsGeneration_admissible

/--
**The start: the root is live and its chime is pending.**

`ExactInitialNetwork.pendingProjected` requires the pending trace to be exactly
the projection of what starting emitted, and `chimer.Initial` emits one chime, so
a start of this plan *must* have it pending. That is where the observation the
commit publishes comes from — it is not put there by hand.
-/
@[reducible] def chiming : chimingPlan.LogicalProcessNetwork where
  instances := fun _ _ => some theRoot
  shared := fun region => region.elim
  inFlight := fun edge => edge.elim
  sessions := fun edge => edge.elim
  obligations := ()
  observations := []
  pending := [Chime.chime]
  usedNominals := startingHistory

/-- And the world after the chime is published. -/
@[reducible] def chimed : chimingPlan.LogicalProcessNetwork :=
  { chiming with observations := [Chime.chime], pending := [] }


/-! ## The start -/

/--
**`chiming` is a start of this plan.**

Every field is the one `Tests/Process/FrontierFixtures.lean`'s `waiting_is_a_start`
carries; the one that does work here is `pendingProjected`, which is why the
chime is pending rather than placed there by hand. `rootInitial` pins
`rootEmitted` to `[Chime.chime]` through `chimer.Initial`, and `pendingProjected`
pins the network's pending trace to that segment's projection under `observeAt`.
Neither is a choice this fixture makes.
-/
def chiming_is_a_start : chimingPlan.ExactInitialNetwork () chiming where
  rootSlot := ()
  root := theRoot
  rootPresent := rfl
  rootKind := rfl
  rootSlotAgrees := rfl
  rootEmitted := [Chime.chime]
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
  sharedInvariantAtStart := fun region => region.elim
  historyFromEmpty := .extend (.refl _) theRootsGeneration theRootsGeneration_admissible

/-! ## The commit -/

/-- **The chime is published**, and it was the one that was pending. -/
theorem the_chime_is_committed : chimingPlan.Commits chiming chimed [Chime.chime] where
  earned := rfl
  appended := rfl
  nonempty := by simp
  scope := by
    intro fragment outside
    match fragment with
    | .instanceState _ _ => rfl
    | .region region => exact region.elim
    | .escrow edge _ => exact edge.elim
    | .session edge _ => exact edge.elim
    | .obligations => rfl
    | .observations => exact absurd ⟨by simp, Or.inl rfl⟩ outside
    | .pending => exact absurd ⟨by simp, Or.inr rfl⟩ outside
    | .nominals => rfl

/-- As a step: a commit allocates nothing, so the history does not move. -/
def theChimeStep : chimingPlan.NetworkStep chiming chimed where
  transition := .commit [Chime.chime] the_chime_is_committed
  admissible := by
    intro nominal allocated
    exact absurd allocated (fun inEmpty => List.not_mem_nil inEmpty)
  historyExact := (NominalHistory.extend_empty _ _).symm

/-! ## The rank: the same structural slack -/

/--
How many parent-spending steps a world can still take.

`Tests/Process/FrontierFixtures.lean`'s `slack`, unchanged, and it is copied
rather than shared because it is about *this* topology's instance type. It is not
a measure of progress — this plan's progress is the chime — but of the finite
bookkeeping its world *type* admits at the worlds no run reaches.
-/
def slack : Option (ProcessInstance chimeTopology) → Nat
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
def rankOf (network : chimingPlan.LogicalProcessNetwork) : Nat :=
  slack (network.instances () ())

/-- **The commit does not descend**: it never touches `instances`, so the rank
either side of it is the live root's zero. -/
theorem rankOf_chiming : rankOf chiming = 0 := rfl

theorem rankOf_chimed : rankOf chimed = 0 := rfl

/-! ## What this plan may install, and what that costs -/

/--
**Anything spawned or restarted here is a root**, because `maySpawn` permits no
parent at all. The same argument `Tests/Process/FrontierFixtures.lean` makes, and
it is repeated rather than shared because it is about *this* topology's
`maySpawn`.
-/
theorem authorized_is_root {incarnation : ProcessInstance chimeTopology}
    (authorized : ∀ parentKind parent,
      incarnation.parentage.knownParent = some ⟨parentKind, parent⟩ →
        chimeTopology.maySpawn parentKind incarnation.kind) :
    incarnation.parentage = .root := by
  cases parentage : incarnation.parentage with
  | root => rfl
  | attached parentKind parent =>
    exact absurd (authorized parentKind parent (by rw [parentage]; rfl)) (fun h => h)
  | detached parentKind parent =>
    exact absurd (authorized parentKind parent (by rw [parentage]; rfl)) (fun h => h)

/-- Detaching spends slack, whether the child is alive or not. -/
theorem slack_detach {before after : ProcessInstance chimeTopology}
    (attached : ∃ parentKind parent, before.parentage = .attached parentKind parent)
    (sameLifecycle : after.lifecycle = before.lifecycle)
    (detached : ∃ parentKind parent, after.parentage = .detached parentKind parent) :
    slack (some after) < slack (some before) := by
  obtain ⟨_, _, isAttached⟩ := attached
  obtain ⟨_, _, isDetached⟩ := detached
  cases lifecycle : before.lifecycle <;>
    simp only [slack, isAttached, isDetached, sameLifecycle, lifecycle] <;> omega

/-- And ending a child spends slack, whichever kind of child it is. -/
theorem slack_end {before after : ProcessInstance chimeTopology}
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

The shared body of `childCancelled` and `childDied`: both carry an `EndsInstance`
and a `wasChild`, and the two together say the incarnation was live, is not, kept
its parentage, and was not the root.
-/
theorem ends_a_child {before after : chimingPlan.LogicalProcessNetwork}
    {ending : ProcessLifecycle (chimeTopology.protocol ())}
    {custody : Bag (chimeTopology.protocol ()).Demand → NoObligations → NoObligations → Prop}
    (wasChild : ∀ incarnation, before.instances () () = some incarnation →
      incarnation.parentage.currentParent ≠ none)
    (step : chimingPlan.EndsInstance before after () () ending custody) :
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

/-! ## Every step of this plan produces, or spends slack -/

/--
**At any world of this plan, a step publishes a chime or the rank descends.**

`NetworkProgressMeasure.descendsOrProduces` for this plan, with the *entropy*
disjunct dropped: there is no entropy-driven step here at all, because
`DrivenByEntropy` is `True` only at a `timeout` — whose edge type is empty — and
at a `processStep` carrying an external event, and `chimer.Step` is `False`.

That is what makes this fixture different from `waitingPlan`, whose
`entropy_or_descends` has the same shape with the *production* disjunct dropped.
Between them the two fixtures inhabit all three of §7's escapes.

The twenty constructors that cannot occur are listed in the module note. Of the
four that remain, `commit` produces and `detach`, `childCancelled` and
`childDied` spend slack.
-/
theorem produces_or_descends {before after : chimingPlan.LogicalProcessNetwork}
    (transition : chimingPlan.NetworkTransition before after) :
    (∃ emitted observation, after.observations = before.observations ++ emitted ∧
        observation = Chime.chime ∧ observation ∈ emitted) ∨
      rankOf after < rankOf before := by
  cases transition with
  | commit emitted step =>
    refine Or.inl ⟨emitted, Chime.chime, step.appended, rfl, ?_⟩
    match emitted, step.nonempty with
    | observation :: _, _ => cases observation; exact List.mem_cons_self ..
  | processStep kind slot _ _ _ _ step =>
    cases kind
    obtain ⟨_, _, _, _, _, _, stepped, _⟩ := step.protocolStep
    exact absurd stepped (fun h => h)
  | spawn kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨fresh, found, _, _⟩ := step.nowLive
    exact absurd
      ((authorized_is_root (step.authorized fresh found)) ▸ rfl :
        fresh.parentage.currentParent = none)
      (step.spawnsAChild fresh found)
  | restart kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨fresh, found, _, _⟩ := step.nowLive
    exact absurd
      ((authorized_is_root (step.authorized fresh found)) ▸ rfl :
        fresh.parentage.currentParent = none)
      (step.restartsAChild fresh found)
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
      | detached _ _ =>
        exact absurd (parentage ▸ rfl : was.parentage.currentParent = none) hadParent
  | childCancelled kind slot _ _ wasChild step =>
    cases kind; cases slot
    exact Or.inr (ends_a_child wasChild step)
  | childDied kind slot _ _ wasChild step =>
    cases kind; cases slot
    exact Or.inr (ends_a_child wasChild step)
  | join kind slot result _ => exact result.elim
  | interrupt _ _ reason _ _ => exact reason.elim
  | fault _ _ f _ _ => exact f.elim
  | environmentViolation _ _ violation _ _ => exact violation.elim
  | processTermination _ _ result _ _ => exact result.elim
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

/-! ## The measure whose progress is a production -/

/--
**A `NetworkProgressMeasure` whose `descendsOrProduces` can take the third
disjunct.**

`waitingMeasure` discharges the obligation from `entropy_or_descends`, and its
`demanded` is `observation.elim`, so §7's production clause could not fire there
even in principle. This one discharges it from `produces_or_descends`: the rank
is the same structural slack, and the commit — the step this plan exists for —
pays with a published observation rather than with rank.

`Reachable := fun _ => True` is again the widest choice, so the obligation is owed
at worlds no run reaches. That is exactly why `produces_or_descends` has a rank
disjunct at all: at an unreachable world holding an attached child, a detach is a
step and it publishes nothing.
-/
def chimingMeasure : chimingPlan.NetworkProgressMeasure chiming where
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  rankTransitive := fun _ _ _ below above => Nat.lt_trans below above
  rank := rankOf
  demanded := fun observation => observation = Chime.chime
  Reachable := fun _ => True
  startIsInitial := ⟨(), ⟨chiming_is_a_start⟩⟩
  reachableStart := trivial
  reachableClosed := fun _ _ => trivial
  descendsOrProduces := fun _ step =>
    (produces_or_descends step.transition).elim
      (fun produces => Or.inr (Or.inr produces))
      (fun descends => Or.inr (Or.inl descends))

/--
**And at the chime step the other two disjuncts are false**, which is what makes
this a witness rather than a coincidence.

`descendsOrProduces` is a disjunction, so a measure can satisfy it while the
production clause never fires — `waitingMeasure` does exactly that, at a plan
where it *cannot* fire. This says the step is not entropy-driven, the rank does
not descend across it, and the production disjunct nevertheless holds. That is
§7's third escape, taken. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.88.

The rank does not descend because a commit's scope is the two observation traces
and `rankOf` reads `instances`, which is the structural reason and not an
accident of this world: `Commits.scope` forbids a commit from touching an
instance at all.
-/
theorem the_chime_takes_the_production_disjunct :
    ¬ theChimeStep.transition.DrivenByEntropy ∧
      ¬ chimingMeasure.rankLt (chimingMeasure.rank chimed) (chimingMeasure.rank chiming) ∧
      (∃ emitted observation, chimed.observations = chiming.observations ++ emitted ∧
        chimingMeasure.demanded observation ∧ observation ∈ emitted) :=
  ⟨id, Nat.lt_irrefl 0, [Chime.chime], Chime.chime, rfl, rfl, List.mem_cons_self ..⟩

/-! ## And then it stops -/

/-- Both networks hold the root, and the root has no parent — the fact the three
parent-spending constructors die on here. -/
theorem chimed_holds_the_root : chimed.instances () () = some theRoot := rfl

theorem the_root_has_no_parent : theRoot.parentage.currentParent = none := rfl

/--
**Nothing happens after the chime.**

`Commits.earned` makes a commit consume what it publishes and `Commits.nonempty`
makes it publish something, so a second commit needs something still pending and
`chimed.pending` is empty. The three steps `produces_or_descends` pays for with
rank all need a current parent, and `chimed` holds the root.

This is the honest boundary of the fixture. It shows §7's production disjunct is
reachable; it does not show an infinite producing run, and this plan cannot,
because the root's initial segment is finite and each observation is published
once.
-/
theorem nothing_happens_after_the_chime {after : chimingPlan.LogicalProcessNetwork}
    (transition : chimingPlan.NetworkTransition chimed after) : False := by
  cases transition with
  | commit committed step =>
    have consumed : ([] : Trace chimeBoundary.Observation) = committed ++ after.pending :=
      step.earned
    exact step.nonempty (List.append_eq_nil_iff.mp consumed.symm).left
  | detach kind slot step =>
    cases kind; cases slot
    obtain ⟨was, foundWas, hadParent⟩ := step.wasAttached
    exact absurd (Option.some.inj (foundWas.symm.trans chimed_holds_the_root) ▸
      the_root_has_no_parent) hadParent
  | childCancelled kind slot _ _ wasChild step =>
    cases kind; cases slot
    exact absurd the_root_has_no_parent (wasChild theRoot chimed_holds_the_root)
  | childDied kind slot _ _ wasChild step =>
    cases kind; cases slot
    exact absurd the_root_has_no_parent (wasChild theRoot chimed_holds_the_root)
  | spawn kind slot _ _ _ step =>
    cases kind; cases slot
    exact absurd (step.wasEmpty.symm.trans chimed_holds_the_root) (by simp)
  | restart kind slot _ _ _ step =>
    cases kind; cases slot
    obtain ⟨old, foundOld, dead⟩ := step.wasEnded
    exact dead (Option.some.inj (foundOld.symm.trans chimed_holds_the_root) ▸
      (ProcessLifecycle.live_iff_running.mpr rfl))
  | processStep kind slot _ _ _ _ step =>
    cases kind
    obtain ⟨_, _, _, _, _, _, stepped, _⟩ := step.protocolStep
    exact absurd stepped (fun h => h)
  | join kind slot result _ => exact result.elim
  | interrupt _ _ reason _ _ => exact reason.elim
  | fault _ _ f _ _ => exact f.elim
  | environmentViolation _ _ violation _ _ => exact violation.elim
  | processTermination _ _ result _ _ => exact result.elim
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

/--
**So `chimed` is at a frontier** — vacuously, in the sense
`Tests/Process/FrontierFixtures.lean`'s `the_empty_world_is_a_frontier` records:
a network nothing can move satisfies "only the outside can move it". The fixture
states it so a reader does not mistake this plan for one whose frontier is a
wait.
-/
theorem the_chimed_world_is_a_frontier : chimingPlan.AtFrontier chimed :=
  fun step => (nothing_happens_after_the_chime step.transition).elim

end Grass.Process.Tests.Chime
