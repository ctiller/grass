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

/-! ## What is owed

The six clauses themselves are not proved here yet, and the two lemmas above are
what a proof of them will be built from. Working the argument clause by clause is
what found `Spawns.spawnsAChild` and `Restarts.restartsAChild`, so the argument is
worth recording even before the mechanisation — with the caveat that this project
has five ledger entries recording defects that did not exist, every one filed from
an argument rather than a construction. Read the following as a plan, not as a
result. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.73.

* `slotsAgree` — `Spawns.slotAgrees` and `Restarts.slotAgrees` for the two
  constructors that install an incarnation; every other instance-touching
  constructor pins `ref` and the kind.
* `lifecyclesWitnessed` — `StepsLocally.stillLive`, `Spawns.nowLive` and
  `Restarts.nowLive` make it vacuous where the incarnation is running, and
  `EndsInstance.endingIsEarned` supplies it where it is not.
* `rootUnique` — `spawnsAChild` and `restartsAChild`, which are the two fields
  this argument produced.
* `parentageValid` — `authorized` for the two installers,
  `ProcessParentage.detach_preserves_knownParent` for `detach`, and pinned
  parentage for the rest.
* `nominalsAllocated` — `allocatesTheGeneration` plus `NetworkStep.historyExact`,
  and `NominalHistory.mem_extend` for the slots a step did not touch.
* `reroutesLand` — every escrow-touching constructor carries `LedgerExtends`, so
  `created` only grows and an arrival that had landed stays landed; `Reroutes`
  carries `arrives` for the resolution it writes.
-/

end ProcessPlan

end Grass.Process
