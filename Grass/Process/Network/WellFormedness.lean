import Grass.Process.Network.Transition

/-!
# Well-formedness is preserved

`Grass/Process/Network/World.lean` says what a well-formed network owes and
`Grass/Process/Network/Transition.lean` says what a step may do. This module is
the theorem the two exist for: **a step of a well-formed network reaches a
well-formed one**.

It is the capstone of the transition family in the sense that it consumes the
fields five review rounds added to it, and it earned its keep before it was
finished: working it clause by clause found three defects that no amount of
reading had.

* `Spawns.authorized` and `Restarts.authorized` read the permitted-parent law off
  the new incarnation's own `knownParent`, so an incarnation recording *no*
  parent discharged them vacuously — and a spawn or a restart could install a
  **root**, which `LogicalProcessNetworkCore.RootUnique` forbids a second of.
  `spawnsAChild` and `restartsAChild` are the fields.
  `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.72.
* No escrow constructor bounded which occurrences *other* than its own it may
  resolve, so a `drop` could append an unrelated occurrence, resolve it
  `.rerouted`, and point it at a session it never touched — breaking
  `ReroutesLand` with every field it had discharged. `ResolvesNothingElse` and
  `ResolvesNothing` are the fields. §10.87.
* And `declared_slot_outcome`'s first payload dropped both the current parent and
  the lifecycle, so two of the six clauses could not be proved from it at all.
  Local adversarial review found that one by exhibiting the root that passes and
  the pair of incarnations that agree on everything reported while disagreeing on
  what the clause asks.

## How it is proved, and why that shape

Every constructor declares at most one `.instanceState` fragment, and
`NetworkTransition.touchesOnly` says a step changes nothing outside its scope. So
**four** of the six clauses — `SlotsAgree`, `LifecyclesWitnessed`,
`ParentageValid` and `NominalsAllocated`, each a property of *one* incarnation in
*one* slot — reduce to a single question per constructor: *at the slot you
declared, does the property still hold?* `instanceProperty_preserved` is that
reduction, and it is the only place the scope discipline is spent.

An earlier version of this note said five, counting `RootUnique`. It does not
fit: `RootUnique` quantifies over **two** slots and concludes they are equal, so
it is not of the form `∀ kind slot incarnation, … → Property kind slot
incarnation` at all. Local adversarial review caught the miscount.
`rootUnique_preserved` uses `declared_slot_outcome` directly, once per slot, and
the bridge it needs is `ProcessParentage.isRoot_of_knownParent_none`: root-ness
is visible in `knownParent`, which is what a carried incarnation agrees on.

The sixth clause, `ReroutesLand`, is about ledgers rather than instances and is
proved separately, from two facts. `ledgers_extend` is the easy one: every
constructor that touches an escrow ledger carries `LedgerExtends`, so `created`
only grows and an arrival that had landed stays landed.
`rerouting_stood_or_is_this_step` is the other, and it did not hold when this
module was started. A `.rerouted` resolution standing after a step had a third
possible origin — a step that resolved an occurrence it never mentioned, because
`LedgerExtends` forbids *erasing* and says nothing about *adding*.
`Tests/Process/RerouteFixtures.lean` builds the `drop` that does it, and
`ResolvesNothingElse` is the field that closes it. §10.87.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

namespace ProcessPlan

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o} {plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations}
  {before after : plan.LogicalProcessNetwork}

/--
**A per-slot property survives a step when it survives at the slot the step
declares.**

The reduction every instance-shaped clause of `WellFormed` uses.
`NetworkTransition.touchesOnly` supplies the other slots: a step changed nothing
outside its scope, and every constructor's scope names at most one instance
fragment, so a slot the step did not declare holds exactly what it held.

Stated over an arbitrary `Property` because the five clauses differ only in what
they ask of the incarnation, and proving the framing five times would be five
chances to get it wrong in a different way.
-/
theorem instanceProperty_preserved
    {Property : ∀ kind : plan.topology.ProcessKind, plan.topology.InstanceId kind →
      ProcessInstance plan.topology → Prop}
    (transition : plan.NetworkTransition before after)
    (held : ∀ kind slot incarnation,
      before.instances kind slot = some incarnation → Property kind slot incarnation)
    (atTheDeclaredSlot : ∀ kind slot incarnation,
      transition.scope (.instanceState kind slot) →
      after.instances kind slot = some incarnation → Property kind slot incarnation) :
    ∀ kind slot incarnation,
      after.instances kind slot = some incarnation → Property kind slot incarnation := by
  intro kind slot incarnation found
  by_cases declared : transition.scope (.instanceState kind slot)
  · exact atTheDeclaredSlot kind slot incarnation declared found
  · exact held kind slot incarnation
      ((transition.touchesOnly (.instanceState kind slot) declared).trans found)

/--
Two instance fragments are the same fragment only when they name the same slot.

The inversion `instanceProperty_preserved`'s users need: a constructor declares
one slot, and a clause is being asked about another, so the two have to be
identified before the constructor's own fields are any use.
-/
theorem instanceFragment_inj {kind kind' : plan.topology.ProcessKind}
    {slot : plan.topology.InstanceId kind} {slot' : plan.topology.InstanceId kind'}
    (equal : (NetworkFragment.instanceState kind slot : NetworkFragment plan.topology)
      = .instanceState kind' slot') :
    ∃ same : kind = kind', same ▸ slot = slot' := by
  cases equal
  exact ⟨rfl, rfl⟩

/-! ## What a step does to the slot it declares -/

/--
Transporting two parentages to a common role and finding them equal is finding
the same recorded parent.
-/
theorem knownParent_of_transported
    {left right : ProcessInstance plan.topology} {kind : plan.topology.ProcessKind}
    (leftKind : left.kind = kind) (rightKind : right.kind = kind)
    (same : leftKind ▸ left.parentage = rightKind ▸ right.parentage) :
    left.parentage.knownParent = right.parentage.knownParent := by
  rw [← ProcessParentage.knownParent_cast leftKind left.parentage,
    ← ProcessParentage.knownParent_cast rightKind right.parentage, same]

/--
And finding one to be the other's detachment is the same, because detaching
removes authority and keeps the parent it knew.
-/
theorem knownParent_of_detached
    {left right : ProcessInstance plan.topology} {kind : plan.topology.ProcessKind}
    (leftKind : left.kind = kind) (rightKind : right.kind = kind)
    (same : leftKind ▸ left.parentage = (rightKind ▸ right.parentage).detach) :
    left.parentage.knownParent = right.parentage.knownParent := by
  rw [← ProcessParentage.knownParent_cast leftKind left.parentage,
    ← ProcessParentage.knownParent_cast rightKind right.parentage, same,
    ProcessParentage.detach_preserves_knownParent]

/-- The six ending constructors carry the identity across in the same way, so
they answer `declared_slot_outcome`'s second disjunct in the same way. -/
theorem endsInstance_carries {kind : plan.topology.ProcessKind}
    {slot : plan.topology.InstanceId kind}
    {ending : ProcessLifecycle (plan.topology.protocol kind)}
    {custody : Bag (plan.topology.protocol kind).Demand → Obligations → Obligations → Prop}
    (step : plan.EndsInstance before after kind slot ending custody)
    (witnessed : ∀ incarnation, after.instances kind slot = some incarnation →
      incarnation.LifecycleWitnessed) :
    ∃ (fromInstance toInstance : ProcessInstance plan.topology)
      (fromKind : fromInstance.kind = kind) (toKind : toInstance.kind = kind),
      before.instances kind slot = some fromInstance ∧
      after.instances kind slot = some toInstance ∧
      toKind ▸ toInstance.ref = fromKind ▸ fromInstance.ref ∧
      toInstance.parentage.knownParent = fromInstance.parentage.knownParent ∧
      (fromInstance.LifecycleWitnessed → toInstance.LifecycleWitnessed) := by
  obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
    sameRef, sameParentage, _⟩ := step.identityPreserved
  exact ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter, sameRef,
    knownParent_of_transported toKind fromKind sameParentage,
    fun _ => witnessed toInstance foundAfter⟩

/--
**An ended incarnation's stored ending is one its protocol reaches.**

`EndsInstance` is the only family that *changes* a lifecycle, so it is the only
one that cannot hand this clause over to the before-network. It does not have to:
`nowEnded` says the stored lifecycle is exactly `ending`, `endingIsEarned` says a
`.terminated` ending is a genuine `ProcessSpec.Terminal` of the state it ended
from, and `identityPreserved` pins the request and the private state those two
are stated over. Decision 129 put `endingIsEarned` there for exactly this, and
this is the first thing to spend it.

The proof destructures both incarnations and eliminates the role equations before
doing anything else, so every `▸` in the fields becomes a transport along `rfl`
and the four facts can be read as the plain equations they are.
-/
theorem endsInstance_witnessed {kind : plan.topology.ProcessKind}
    {slot : plan.topology.InstanceId kind}
    {ending : ProcessLifecycle (plan.topology.protocol kind)}
    {custody : Bag (plan.topology.protocol kind).Demand → Obligations → Obligations → Prop}
    (step : plan.EndsInstance before after kind slot ending custody)
    {incarnation : ProcessInstance plan.topology}
    (found : after.instances kind slot = some incarnation) :
    incarnation.LifecycleWitnessed := by
  obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
    _, _, sameRequest, sameLocal⟩ := step.identityPreserved
  obtain ⟨endedInstance, foundEnded, endedKind, isEnding⟩ := step.nowEnded
  obtain ⟨earnedInstance, earnedKind, foundEarned, terminalCase, _⟩ := step.endingIsEarned
  have sameTo : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
  subst sameTo
  have sameEnded : endedInstance = toInstance :=
    Option.some.inj (foundEnded.symm.trans foundAfter)
  subst sameEnded
  have sameFrom : earnedInstance = fromInstance :=
    Option.some.inj (foundEarned.symm.trans foundBefore)
  subst sameFrom
  cases earnedInstance with
  | mk fromRole fromRef fromParentage fromRequest fromLocal fromOutstanding fromLifecycle =>
  cases endedInstance with
  | mk toRole toRef toParentage toRequest toLocal toOutstanding toLifecycle =>
  cases toKind
  cases fromKind
  have storedEnding : toLifecycle = ending := isEnding
  have request : toRequest = fromRequest := sameRequest
  have local' : toLocal = fromLocal := sameLocal
  intro result ended
  rw [request, local']
  exact terminalCase result (storedEnding.symm.trans ended)

/--
**Three things a step can do to the slot it declared, and no fourth.**

The case analysis every instance-shaped clause of `WellFormed` shares, done once.
Twenty-four constructors, thirteen of which declare no instance fragment at all —
for those the declaration is absurd. Of the eleven that remain:

* `join` empties the slot, and a clause about what a slot holds asks nothing of
  an empty one;
* `processStep`, `detach` and the six endings *carry* an incarnation across,
  agreeing on the reference and on the parent it knows, so the before-network
  answers for it. They allocate nothing, which is what `¬ scope .nominals`
  records — the clause about allocation needs it and cannot get it from the
  identity fields — and they hand `LifecycleWitnessed` over, which the endings do
  by earning the ending rather than by inheriting it;
* `spawn` and `restart` *install* one and answer for it themselves, with
  `slotAgrees`, `authorized`, `allocatesTheGeneration`, `spawnsAChild` and
  `nowLive`.

Doing this once rather than once per clause is the difference between one
twenty-four-way split and four, and it puts the constructor names in one place: a
new constructor breaks this proof and nothing else.

**Two conjuncts here are review's, and both were missing.** The first payload
reported only the reference and the known parent, which cannot settle
`LifecyclesWitnessed` — a reviewer exhibited two incarnations agreeing on both
where one is witnessed and the other is not — and reported nothing about a
current parent, which cannot settle `RootUnique`: a *root* satisfies every
conjunct the installed case reported, `authorized` vacuously among them, since
a root has no known parent to authorize. `spawnsAChild` is what refuses it, and
dropping that field here dropped precisely the field the module header says it
was added for.
-/
theorem declared_slot_outcome (transition : plan.NetworkTransition before after)
    {kind : plan.topology.ProcessKind} {slot : plan.topology.InstanceId kind}
    (declared : transition.scope (.instanceState kind slot)) :
    after.instances kind slot = none
    ∨ (¬ transition.scope .nominals ∧
        ∃ (fromInstance toInstance : ProcessInstance plan.topology)
          (fromKind : fromInstance.kind = kind) (toKind : toInstance.kind = kind),
          before.instances kind slot = some fromInstance ∧
          after.instances kind slot = some toInstance ∧
          toKind ▸ toInstance.ref = fromKind ▸ fromInstance.ref ∧
          toInstance.parentage.knownParent = fromInstance.parentage.knownParent ∧
          (fromInstance.LifecycleWitnessed → toInstance.LifecycleWitnessed))
    ∨ (∀ incarnation, after.instances kind slot = some incarnation →
        (∃ sameKind : incarnation.kind = kind,
          sameKind ▸ incarnation.ref.instanceId = slot) ∧
        (∀ parentKind parent,
          incarnation.parentage.knownParent = some ⟨parentKind, parent⟩ →
          plan.topology.maySpawn parentKind incarnation.kind) ∧
        incarnation.ref.generation ∈ transition.allocatedNominals.entries ∧
        incarnation.Live ∧
        incarnation.parentage.currentParent ≠ none) := by
  cases transition with
  | processStep _ _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h | ⟨_, _, h⟩
          · exact h
          · exact absurd h.2 (by intro equal; cases equal)
          · exact absurd h (by intro equal; cases equal))
    cases same; cases sameSlot
    obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter, _, _,
      sameRef, sameParentage, _⟩ := step.protocolStep
    obtain ⟨live, foundLive, isLive⟩ := step.stillLive
    refine Or.inr (Or.inl ⟨(by rintro (h | ⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h),
      fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter, sameRef,
      knownParent_of_transported toKind fromKind sameParentage, fun _ => ?_⟩)
    exact ProcessInstance.live_witnessed_vacuously
      (Option.some.inj (foundLive.symm.trans foundAfter) ▸ isLive)
  | detach _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj declared
    cases same; cases sameSlot
    obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
      isDetach, sameLifecycle, sameRef, sameRequest, sameLocal, _⟩ := step.identityPreserved
    exact Or.inr (Or.inl ⟨(by intro h; cases h),
      fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter, sameRef,
      knownParent_of_detached toKind fromKind isDetach,
      ProcessInstance.lifecycleWitnessed_transfer toKind fromKind sameLifecycle
        sameRequest sameLocal⟩)
  | join _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj declared
    cases same; cases sameSlot
    exact Or.inl step.nowFree
  | spawn _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h | h
          · exact h
          · exact absurd h (by intro equal; cases equal)
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    refine Or.inr (Or.inr fun incarnation found => ⟨step.slotAgrees incarnation found,
      step.authorized incarnation found, step.allocatesTheGeneration incarnation found, ?_,
      step.spawnsAChild incarnation found⟩)
    obtain ⟨live, foundLive, isLive, _⟩ := step.nowLive
    exact Option.some.inj (foundLive.symm.trans found) ▸ isLive
  | restart _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h | h
          · exact h
          · exact absurd h (by intro equal; cases equal)
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    refine Or.inr (Or.inr fun incarnation found => ⟨step.slotAgrees incarnation found,
      step.authorized incarnation found, step.allocatesTheGeneration incarnation found, ?_,
      step.restartsAChild incarnation found⟩)
    obtain ⟨live, foundLive, isLive, _⟩ := step.nowLive
    exact Option.some.inj (foundLive.symm.trans found) ▸ isLive
  | interrupt _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact Or.inr (Or.inl ⟨(by rintro (h | ⟨_, h⟩) <;> cases h),
      endsInstance_carries step (fun _ => endsInstance_witnessed step)⟩)
  | fault _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact Or.inr (Or.inl ⟨(by rintro (h | ⟨_, h⟩) <;> cases h),
      endsInstance_carries step (fun _ => endsInstance_witnessed step)⟩)
  | environmentViolation _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact Or.inr (Or.inl ⟨(by rintro (h | ⟨_, h⟩) <;> cases h),
      endsInstance_carries step (fun _ => endsInstance_witnessed step)⟩)
  | childCancelled _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact Or.inr (Or.inl ⟨(by rintro (h | ⟨_, h⟩) <;> cases h),
      endsInstance_carries step (fun _ => endsInstance_witnessed step)⟩)
  | childDied _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact Or.inr (Or.inl ⟨(by rintro (h | ⟨_, h⟩) <;> cases h),
      endsInstance_carries step (fun _ => endsInstance_witnessed step)⟩)
  | processTermination _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact Or.inr (Or.inl ⟨(by rintro (h | ⟨_, h⟩) <;> cases h),
      endsInstance_carries step (fun _ => endsInstance_witnessed step)⟩)
  | send _ _ _ _ => exact absurd declared (by intro equal; cases equal)
  | requestCancel _ _ _ _ => exact absurd declared (by intro equal; cases equal)
  | acknowledgeCancel _ _ _ _ _ => exact absurd declared (by intro equal; cases equal)
  | timeout _ _ _ _ => exact absurd declared (by intro equal; cases equal)
  | senderDeath _ _ _ _ _ => exact absurd declared (by intro equal; cases equal)
  | receiverDeath _ _ _ _ _ => exact absurd declared (by intro equal; cases equal)
  | drop _ _ _ _ => exact absurd declared (by intro equal; cases equal)
  | coalesce _ _ _ _ _ => exact absurd declared (by intro equal; cases equal)
  | commit _ _ =>
    rcases declared.2 with h | h <;> exact absurd h (by intro equal; cases equal)
  | receive _ _ _ _ =>
    rcases declared with h | h <;> exact absurd h (by intro equal; cases equal)
  | channelClose _ _ _ _ =>
    rcases declared with h | h <;> exact absurd h (by intro equal; cases equal)
  | channelDeath _ _ _ _ =>
    rcases declared with h | h <;> exact absurd h (by intro equal; cases equal)
  | reroute _ _ _ _ _ =>
    rcases declared with h | h <;> exact absurd h (by intro equal; cases equal)

/-! ## The clauses -/

/--
**A step preserves the validity of recorded parenthood.**

`docs/DECISIONS.md` decision 130's law. A carried incarnation knows the parent
the one before it knew, and the before-network answered for that; an installed
one answers with `authorized`, which is the law itself; an emptied slot has
nothing to answer for.
-/
theorem parentageValid_preserved (transition : plan.NetworkTransition before after)
    (valid : before.ParentageValid) : after.ParentageValid := by
  refine instanceProperty_preserved
    (Property := fun _ _ incarnation => ∀ parentKind parent,
      incarnation.parentage.knownParent = some ⟨parentKind, parent⟩ →
        plan.topology.maySpawn parentKind incarnation.kind)
    transition valid ?_
  intro kind slot incarnation declared found
  rcases declared_slot_outcome transition declared with empty | ⟨_, carried⟩ | installed
  · exact absurd (empty.symm.trans found) (by intro equal; cases equal)
  · obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
      _, sameKnown, _⟩ := carried
    have same : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
    subst same
    intro parentKind parent known
    have permitted :=
      valid kind slot fromInstance foundBefore parentKind parent (sameKnown ▸ known)
    rw [toKind, ← fromKind]
    exact permitted
  · exact (installed incarnation found).2.1

/--
**A step preserves the agreement between a slot and what it holds.**

The clause that stopped a spawn installing an incarnation naming slot 3 into slot
7. A carried incarnation has the reference the one before it had, and the
before-network placed that correctly; an installed one answers with `slotAgrees`,
which is the field local adversarial review put there.
-/
theorem slotsAgree_preserved (transition : plan.NetworkTransition before after)
    (agree : before.SlotsAgree) : after.SlotsAgree := by
  refine instanceProperty_preserved
    (Property := fun kind slot incarnation => ∃ sameKind : incarnation.kind = kind,
      (sameKind ▸ incarnation.ref.instanceId : plan.topology.InstanceId kind) = slot)
    transition agree ?_
  intro kind slot incarnation declared found
  rcases declared_slot_outcome transition declared with empty | ⟨_, carried⟩ | installed
  · exact absurd (empty.symm.trans found) (by intro equal; cases equal)
  · obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
      sameRef, _, _⟩ := carried
    have same : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
    subst same
    obtain ⟨_, atSlot⟩ := agree kind slot fromInstance foundBefore
    refine ⟨toKind, ?_⟩
    rw [← ProcessTopologyCore.ProcessRef.instanceId_cast toKind toInstance.ref, sameRef,
      ProcessTopologyCore.ProcessRef.instanceId_cast fromKind fromInstance.ref]
    exact atSlot
  · exact (installed incarnation found).1

/--
**A step preserves the allocation of every live generation.**

`docs/FOUNDATION.md` law 22 at the network, and the one clause that is a law of
`NetworkStep` rather than of `NetworkTransition`: `usedNominals` moves by
`historyExact`, which is a field of the step and not of the transition. A
transition alone can shrink the history and strand every generation in it.

The history only grows, so a carried incarnation — whose reference is the one it
had — stays allocated. An installed one has a generation this step allocated, and
`NetworkStep.allocations_are_recorded` puts it in the history afterwards.
-/
theorem nominalsAllocated_preserved (step : plan.NetworkStep before after)
    (allocated : before.NominalsAllocated) : after.NominalsAllocated := by
  have grows : ∀ nominal ∈ before.usedNominals.used, nominal ∈ after.usedNominals.used := by
    intro nominal member
    rw [step.historyExact]
    exact NominalHistory.mem_extend.mpr (Or.inr member)
  refine instanceProperty_preserved
    (Property := fun _ _ incarnation => incarnation.ref.Allocated after.usedNominals)
    step.transition
    (fun kind slot incarnation found => grows _ (allocated kind slot incarnation found)) ?_
  intro kind slot incarnation declared found
  rcases declared_slot_outcome step.transition declared with empty | ⟨_, carried⟩ | installed
  · exact absurd (empty.symm.trans found) (by intro equal; cases equal)
  · obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
      sameRef, _, _⟩ := carried
    have same : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
    subst same
    have sameGeneration : toInstance.ref.generation = fromInstance.ref.generation := by
      rw [← ProcessTopologyCore.ProcessRef.generation_cast toKind toInstance.ref, sameRef,
        ProcessTopologyCore.ProcessRef.generation_cast fromKind fromInstance.ref]
    show toInstance.ref.generation ∈ after.usedNominals.used
    rw [sameGeneration]
    exact grows _ (allocated kind slot fromInstance foundBefore)
  · exact step.allocations_are_recorded (installed incarnation found).2.2.1

/--
**A step preserves the correspondence between a stored ending and the protocol.**

`docs/DECISIONS.md` decision 129 puts this at the network:
`Grass/Process/Network/Instance.lean` states the per-instance predicate and says
it cannot enforce it, having no network to enforce it over. This is the
enforcement, across every step.

`processStep` and `spawn`/`restart` discharge it vacuously and honestly — a live
incarnation is under no terminal obligation, which is what makes a running
process representable at all. `detach` transfers it. The six endings are the only
constructors that *change* a lifecycle, and they earn it with `endingIsEarned`
rather than inheriting it.
-/
theorem lifecyclesWitnessed_preserved (transition : plan.NetworkTransition before after)
    (witnessed : before.LifecyclesWitnessed) : after.LifecyclesWitnessed := by
  refine instanceProperty_preserved
    (Property := fun _ _ incarnation => incarnation.LifecycleWitnessed)
    transition witnessed ?_
  intro kind slot incarnation declared found
  rcases declared_slot_outcome transition declared with empty | ⟨_, carried⟩ | installed
  · exact absurd (empty.symm.trans found) (by intro equal; cases equal)
  · obtain ⟨fromInstance, toInstance, _, _, foundBefore, foundAfter, _, _, transfer⟩ := carried
    have same : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
    subst same
    exact transfer (witnessed kind slot fromInstance foundBefore)
  · exact ProcessInstance.live_witnessed_vacuously (installed incarnation found).2.2.2.1

/-! ## Root uniqueness, which is not a per-slot property -/

/--
**A root found in a slot after a step was a root in that slot before it.**

The bridge `rootUnique_preserved` needs, and the reason it cannot go through
`instanceProperty_preserved`: `RootUnique` relates *two* slots, so it is not of
the form that reduction takes. What is per-slot is this — root-ness came from
somewhere — and root uniqueness then follows from the before-network's, applied
once.

Each of `declared_slot_outcome`'s three outcomes answers:

* an emptied slot holds no root, because it holds nothing;
* a carried incarnation knows the parent the one before it knew, and
  `ProcessParentage.isRoot_of_knownParent_none` says root-ness *is* knowing no
  parent — so root-ness travels with `knownParent` in both directions;
* an installed one has a current parent, by `Spawns.spawnsAChild`, and a root has
  none. This is the case that was open until local adversarial review pointed out
  that `declared_slot_outcome` had dropped that field: every other conjunct the
  installed case reports is satisfied by a root, `authorized` vacuously among
  them, since a root has no known parent to authorize.
-/
theorem root_was_there (transition : plan.NetworkTransition before after)
    {slot : plan.topology.InstanceId plan.topology.root}
    {incarnation : ProcessInstance plan.topology}
    (found : after.instances plan.topology.root slot = some incarnation)
    (isRoot : incarnation.IsRoot) :
    ∃ earlier, before.instances plan.topology.root slot = some earlier ∧ earlier.IsRoot := by
  by_cases declared : transition.scope (.instanceState plan.topology.root slot)
  · rcases declared_slot_outcome transition declared with empty | ⟨_, carried⟩ | installed
    · exact absurd (empty.symm.trans found) (by intro equal; cases equal)
    · obtain ⟨fromInstance, toInstance, _, _, foundBefore, foundAfter, _, sameKnown, _⟩ := carried
      have same : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
      subst same
      exact ⟨fromInstance, foundBefore, ProcessParentage.isRoot_of_knownParent_none
        (sameKnown ▸ ProcessParentage.knownParent_eq_none_of_isRoot isRoot)⟩
    · exact absurd (ProcessParentage.root_currentParent isRoot)
        (installed incarnation found).2.2.2.2
  · exact ⟨incarnation,
      (transition.touchesOnly (.instanceState plan.topology.root slot) declared).trans found,
      isRoot⟩

/--
**A step preserves root uniqueness.**

`docs/DECISIONS.md` decision 130's other law. Both roots after the step were
roots before it, in the same slots, and the before-network already said two roots
are one slot.
-/
theorem rootUnique_preserved (transition : plan.NetworkTransition before after)
    (unique : before.RootUnique) : after.RootUnique := by
  intro leftSlot rightSlot leftInstance rightInstance foundLeft foundRight leftRoot rightRoot
  obtain ⟨leftEarlier, foundLeftEarlier, leftEarlierRoot⟩ :=
    root_was_there transition foundLeft leftRoot
  obtain ⟨rightEarlier, foundRightEarlier, rightEarlierRoot⟩ :=
    root_was_there transition foundRight rightRoot
  exact unique leftSlot rightSlot leftEarlier rightEarlier foundLeftEarlier foundRightEarlier
    leftEarlierRoot rightEarlierRoot

/-! ## Reroutes land, which is about ledgers rather than slots -/

/-- Two escrow fragments are the same fragment only when they name the same
session of the same edge. -/
theorem escrowFragment_inj {edge edge' : plan.topology.ChannelKind}
    {session : plan.topology.ChannelId edge} {session' : plan.topology.ChannelId edge'}
    (equal : (NetworkFragment.escrow edge session : NetworkFragment plan.topology)
      = .escrow edge' session') :
    ∃ same : edge = edge', same ▸ session = session' := by
  cases equal
  exact ⟨rfl, rfl⟩

/-- A session whose escrow a step did not declare holds exactly what it held. -/
theorem ledger_unchanged (transition : plan.NetworkTransition before after)
    {edge : plan.topology.ChannelKind} {session : plan.topology.ChannelId edge}
    (outside : ¬ transition.scope (.escrow edge session)) :
    before.inFlight edge session = after.inFlight edge session :=
  transition.touchesOnly (.escrow edge session) outside

/--
**Every session's escrow ledger only moves forward across a step.**

`LedgerExtends` is a per-ledger law each escrow-touching constructor carries for
the session it declares. This is the whole-network form: a session the step did
not declare is unchanged, and a session it did declare carries the law. It is
what lets `reroutesLand_preserved` say an arrival that had landed stays landed —
the destination is generally *not* the session the step is about, so nothing in
that step's own fields mentions it.
-/
theorem ledgers_extend (transition : plan.NetworkTransition before after)
    (edge : plan.topology.ChannelKind) (session : plan.topology.ChannelId edge) :
    LedgerExtends (before.inFlight edge session) (after.inFlight edge session) := by
  by_cases declared : transition.scope (.escrow edge session)
  · cases transition with
    | send _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact step.ledgerExtends
    | receive _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj
        (by rcases declared with h | h
            · exact h
            · exact absurd h (by intro equal; cases equal))
      cases same; cases sameSession
      exact step.ledgerExtends
    | requestCancel _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact step.ledgerExtends
    | acknowledgeCancel _ _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact step.ledgerExtends
    | timeout _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact step.ledgerExtends
    | senderDeath _ _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact step.ledgerExtends
    | receiverDeath _ _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact step.ledgerExtends
    | drop _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact step.ledgerExtends
    | coalesce _ _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact step.ledgerExtends
    | channelClose _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj
        (by rcases declared with h | h
            · exact h
            · exact absurd h (by intro equal; cases equal))
      cases same; cases sameSession
      exact step.ledgerExtends
    | channelDeath _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj
        (by rcases declared with h | h
            · exact h
            · exact absurd h (by intro equal; cases equal))
      cases same; cases sameSession
      exact step.ledgerExtends
    | reroute _ _ _ _ step =>
      rcases declared with h | h
      · obtain ⟨same, sameSession⟩ := escrowFragment_inj h
        cases same; cases sameSession
        exact step.ledgerExtends
      · obtain ⟨same, sameSession⟩ := escrowFragment_inj h
        cases same; cases sameSession
        exact step.destinationExtends
    | processStep _ _ _ _ _ _ _ =>
      exact absurd declared (by rintro (h | ⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h)
    | spawn _ _ _ _ _ _ => exact absurd declared (by rintro (h | h | ⟨_, h⟩) <;> cases h)
    | restart _ _ _ _ _ _ => exact absurd declared (by rintro (h | h | ⟨_, h⟩) <;> cases h)
    | join _ _ _ _ => exact absurd declared (by intro equal; cases equal)
    | detach _ _ _ => exact absurd declared (by intro equal; cases equal)
    | interrupt _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | fault _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | environmentViolation _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | childCancelled _ _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | childDied _ _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | processTermination _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | commit _ _ =>
      rcases declared.2 with h | h <;> exact absurd h (by intro equal; cases equal)
  · exact ledger_unchanged transition declared ▸ LedgerExtends.refl _

/--
**A `.rerouted` resolution standing after a step either stood before it, or is
the reroute that wrote it.**

The other half of the sixth clause, and the half that did not exist until a
construction forced it. `ResolvesNothingElse` is what makes the disjunction
exhaustive: without it a step could resolve an occurrence it never mentioned, and
there was a third case — a `.rerouted` resolution belonging to no constructor,
pointing at a session nothing had touched. `Tests/Process/RerouteFixtures.lean`
builds that step and `the_stranding_drop_is_refused` is it being refused.
-/
theorem rerouting_stood_or_is_this_step (transition : plan.NetworkTransition before after)
    {edge : plan.topology.ChannelKind} {session : plan.topology.ChannelId edge}
    {occurrence : EdgeOccurrence plan.topology plan.message edge}
    {destination : plan.topology.ChannelId edge}
    (resolved : (after.inFlight edge session).resolution occurrence
      = some (.rerouted destination)) :
    (before.inFlight edge session).resolution occurrence = some (.rerouted destination)
    ∨ ∃ arrival, arrival ∈ (after.inFlight edge destination).created := by
  by_cases declared : transition.scope (.escrow edge session)
  · cases transition with
    | reroute _ session' occurrence' destination' step =>
      rcases declared with h | h
      · obtain ⟨same, sameSession⟩ := escrowFragment_inj h
        cases same; cases sameSession
        by_cases isIt : occurrence = occurrence'
        · subst isIt
          obtain ⟨arrival, _, arrived, _⟩ := step.arrives
          have sameDestination : destination' = destination := by
            rw [step.nowResolved] at resolved
            cases resolved
            rfl
          subst sameDestination
          exact Or.inr ⟨arrival, arrived⟩
        · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
      · obtain ⟨same, sameSession⟩ := escrowFragment_inj h
        cases same; cases sameSession
        exact Or.inl (step.destinationResolvesNothing occurrence ▸ resolved)
    | send _ _ occurrence' step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact Or.inl (step.resolvesNothing occurrence ▸ resolved)
    | requestCancel _ _ _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      exact Or.inl (step.resolvesNothing occurrence ▸ resolved)
    | receive _ _ occurrence' step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj
        (by rcases declared with h | h
            · exact h
            · exact absurd h (by intro equal; cases equal))
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | channelClose _ _ occurrence' step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj
        (by rcases declared with h | h
            · exact h
            · exact absurd h (by intro equal; cases equal))
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | channelDeath _ _ occurrence' step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj
        (by rcases declared with h | h
            · exact h
            · exact absurd h (by intro equal; cases equal))
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | acknowledgeCancel _ _ occurrence' _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | timeout _ _ occurrence' step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | senderDeath _ _ occurrence' _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | receiverDeath _ _ occurrence' _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | drop _ _ occurrence' step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | coalesce _ _ occurrence' _ step =>
      obtain ⟨same, sameSession⟩ := escrowFragment_inj declared
      cases same; cases sameSession
      by_cases isIt : occurrence = occurrence'
      · subst isIt
        rw [step.nowResolved] at resolved
        exact absurd resolved (by intro equal; cases equal)
      · exact Or.inl (step.resolvesNothingElse occurrence isIt ▸ resolved)
    | processStep _ _ _ _ _ _ _ =>
      exact absurd declared (by rintro (h | ⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h)
    | spawn _ _ _ _ _ _ => exact absurd declared (by rintro (h | h | ⟨_, h⟩) <;> cases h)
    | restart _ _ _ _ _ _ => exact absurd declared (by rintro (h | h | ⟨_, h⟩) <;> cases h)
    | join _ _ _ _ => exact absurd declared (by intro equal; cases equal)
    | detach _ _ _ => exact absurd declared (by intro equal; cases equal)
    | interrupt _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | fault _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | environmentViolation _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | childCancelled _ _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | childDied _ _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | processTermination _ _ _ _ _ => exact absurd declared (by rintro (h | ⟨_, h⟩) <;> cases h)
    | commit _ _ =>
      rcases declared.2 with h | h <;> exact absurd h (by intro equal; cases equal)
  · exact Or.inl (ledger_unchanged transition declared ▸ resolved)

/--
**A step preserves the landing of every rerouted occurrence.**

`WellFormed`'s sixth clause, and the one that is about ledgers rather than slots.
A `.rerouted` resolution standing afterwards either stood before — and the
before-network found it an arrival, which `ledgers_extend` says is still there —
or is this step's own, and `Reroutes.arrives` is the arrival.
-/
theorem reroutesLand_preserved (transition : plan.NetworkTransition before after)
    (lands : before.ReroutesLand) : after.ReroutesLand := by
  intro edge session occurrence destination resolved
  rcases rerouting_stood_or_is_this_step transition resolved with stood | ⟨arrival, arrived⟩
  · obtain ⟨arrival, arrived⟩ := lands edge session occurrence destination stood
    exact ⟨arrival, (ledgers_extend transition edge destination).created_preserved arrived⟩
  · exact ⟨arrival, arrived⟩

/-! ## The capstone -/

/--
**A step of a well-formed network reaches a well-formed one.**

`docs/PROCESS.md` §3's obligation, and the theorem this module exists for. Stated
over `NetworkStep` rather than `NetworkTransition` because one clause genuinely
needs the step: `usedNominals` moves by `historyExact`, which is a field of the
step, and a spawn *transition* alone may install a generation and record nothing.
-/
theorem wellFormed_preserved (step : plan.NetworkStep before after)
    (wellFormed : before.WellFormed) : after.WellFormed where
  slotsAgree := slotsAgree_preserved step.transition wellFormed.slotsAgree
  lifecyclesWitnessed :=
    lifecyclesWitnessed_preserved step.transition wellFormed.lifecyclesWitnessed
  rootUnique := rootUnique_preserved step.transition wellFormed.rootUnique
  parentageValid := parentageValid_preserved step.transition wellFormed.parentageValid
  nominalsAllocated := nominalsAllocated_preserved step wellFormed.nominalsAllocated
  reroutesLand := reroutesLand_preserved step.transition wellFormed.reroutesLand

end ProcessPlan

end Grass.Process
