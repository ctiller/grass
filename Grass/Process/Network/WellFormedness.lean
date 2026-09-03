import Grass.Process.Network.Transition

/-!
# Well-formedness is preserved

`Grass/Process/Network/World.lean` says what a well-formed network owes and
`Grass/Process/Network/Transition.lean` says what a step may do. This module is
the theorem the two exist for: **a step of a well-formed network reaches a
well-formed one**.

It is the capstone of the transition family in the sense that it consumes the
fields five review rounds added to it, and it earned its keep before it was
finished: working it clause by clause found two defects that no amount of reading
had. `Spawns.authorized` and `Restarts.authorized` read the permitted-parent law
off the new incarnation's own `knownParent`, so an incarnation recording *no*
parent discharged them vacuously — and a spawn or a restart could install a
**root**, which `LogicalProcessNetworkCore.RootUnique` forbids a second of.
`spawnsAChild` and `restartsAChild` are the fields, and
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.72 is the entry.

## How it is proved, and why that shape

Every constructor declares at most one `.instanceState` fragment, and
`NetworkTransition.touchesOnly` says a step changes nothing outside its scope. So
five of the six clauses — every one that quantifies over slots — reduce to a
single question per constructor: *at the slot you declared, does the property
still hold?* `instanceProperty_preserved` is that reduction, and it is the only
place the scope discipline is spent.

The sixth clause, `ReroutesLand`, is about ledgers rather than instances and is
proved separately. It turns on one fact: every constructor that touches an escrow
ledger carries `LedgerExtends`, so `created` only ever grows, and an arrival that
had landed stays landed.
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

/-! ## Parentage -/

/--
An incarnation that records the parent another one recorded inherits its
validity.

The shared body of eight of `parentageValid_preserved`'s cases. Whether the
parentage was *pinned* (`processStep`, the six endings) or *moved* (`detach`,
which changes `attached` to `detached` and keeps the reference), what the clause
reads is `knownParent`, and that is what these constructors agree on.
-/
theorem parentage_transfers (valid : before.ParentageValid)
    {kind : plan.topology.ProcessKind} {slot : plan.topology.InstanceId kind}
    {fromInstance toInstance : ProcessInstance plan.topology}
    (fromKind : fromInstance.kind = kind) (toKind : toInstance.kind = kind)
    (foundBefore : before.instances kind slot = some fromInstance)
    (sameKnown : toInstance.parentage.knownParent = fromInstance.parentage.knownParent) :
    ∀ parentKind parent, toInstance.parentage.knownParent = some ⟨parentKind, parent⟩ →
      plan.topology.maySpawn parentKind toInstance.kind := by
  intro parentKind parent known
  have permitted :=
    valid kind slot fromInstance foundBefore parentKind parent (sameKnown ▸ known)
  rw [toKind, ← fromKind]
  exact permitted

/-- And the six ending constructors all pin the parentage, so they all inherit
it the same way. -/
theorem endsInstance_parentage (valid : before.ParentageValid)
    {kind : plan.topology.ProcessKind} {slot : plan.topology.InstanceId kind}
    {ending : ProcessLifecycle (plan.topology.protocol kind)}
    {custody : Bag (plan.topology.protocol kind).Demand → Obligations → Obligations → Prop}
    {incarnation : ProcessInstance plan.topology}
    (found : after.instances kind slot = some incarnation)
    (step : plan.EndsInstance before after kind slot ending custody) :
    ∀ parentKind parent, incarnation.parentage.knownParent = some ⟨parentKind, parent⟩ →
      plan.topology.maySpawn parentKind incarnation.kind := by
  obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
    _, sameParentage, _⟩ := step.identityPreserved
  have same : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
  subst same
  refine parentage_transfers valid fromKind toKind foundBefore ?_
  rw [← ProcessParentage.knownParent_cast toKind toInstance.parentage,
    ← ProcessParentage.knownParent_cast fromKind fromInstance.parentage, sameParentage]

/--
**A step preserves the validity of recorded parenthood.**

`docs/DECISIONS.md` decision 130's law, and the first clause of the capstone this
module is for. Six kinds of constructor can put an incarnation in a slot and each
answers for the parent it records:

* `spawn` and `restart` answer with `authorized`, which is the law itself;
* `processStep` and the six endings pin the parentage, so the before-network
  answers;
* `detach` moves it from `attached` to `detached`, which
  `ProcessParentage.detach_preserves_knownParent` says keeps the recorded parent;
* `join` empties the slot, so there is nothing to answer for.

Everything else declares no instance fragment and is
`instanceProperty_preserved`'s other branch.
-/
theorem parentageValid_preserved (transition : plan.NetworkTransition before after)
    (valid : before.ParentageValid) : after.ParentageValid := by
  refine instanceProperty_preserved
    (Property := fun _ _ incarnation => ∀ parentKind parent,
      incarnation.parentage.knownParent = some ⟨parentKind, parent⟩ →
        plan.topology.maySpawn parentKind incarnation.kind)
    transition valid ?_
  intro kind slot incarnation declared found
  cases transition with
  | processStep _ _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h | ⟨_, _, h⟩
          · exact h
          · exact absurd h.2 (by intro equal; cases equal)
          · exact absurd h (by intro equal; cases equal))
    cases same; cases sameSlot
    obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter, _, _,
      _, sameParentage, _⟩ := step.protocolStep
    have same : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
    subst same
    refine parentage_transfers valid fromKind toKind foundBefore ?_
    rw [← ProcessParentage.knownParent_cast toKind toInstance.parentage,
      ← ProcessParentage.knownParent_cast fromKind fromInstance.parentage, sameParentage]
  | spawn _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h | h
          · exact h
          · exact absurd h (by intro equal; cases equal)
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact step.authorized incarnation found
  | restart _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h | h
          · exact h
          · exact absurd h (by intro equal; cases equal)
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact step.authorized incarnation found
  | detach _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj declared
    cases same; cases sameSlot
    obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
      isDetach, _⟩ := step.identityPreserved
    have same : toInstance = incarnation := Option.some.inj (foundAfter.symm.trans found)
    subst same
    refine parentage_transfers valid fromKind toKind foundBefore ?_
    rw [← ProcessParentage.knownParent_cast toKind toInstance.parentage,
      ← ProcessParentage.knownParent_cast fromKind fromInstance.parentage, isDetach,
      ProcessParentage.detach_preserves_knownParent]
  | join _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj declared
    cases same; cases sameSlot
    exact absurd (step.nowFree.symm.trans found) (by intro equal; cases equal)
  | interrupt _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact endsInstance_parentage valid found step
  | fault _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact endsInstance_parentage valid found step
  | environmentViolation _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact endsInstance_parentage valid found step
  | childCancelled _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact endsInstance_parentage valid found step
  | childDied _ _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact endsInstance_parentage valid found step
  | processTermination _ _ _ _ step =>
    obtain ⟨same, sameSlot⟩ := instanceFragment_inj
      (by rcases declared with h | h
          · exact h
          · exact absurd h.2 (by intro equal; cases equal))
    cases same; cases sameSlot
    exact endsInstance_parentage valid found step
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


end ProcessPlan

end Grass.Process
