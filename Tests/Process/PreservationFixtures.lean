import Grass.Process.Network.WellFormedness
import Tests.Process.LifecycleStepFixtures
import Tests.Process.RerouteFixtures

/-!
# The capstone, spent

`ProcessPlan.wellFormed_preserved` says a step of a well-formed network reaches a
well-formed one. This file applies it, and the application is worth having for a
reason beyond coverage: it turns a **vacuous** certificate into a **non-vacuous**
one.

`Tests/Process/WorldFixtures.lean`'s `quiet_is_wellFormed` discharges all six
clauses from "the network holds nothing" — every one is `absurd found`. That is
honest and it certifies nothing about any instance, because there are none.
`spawned_is_wellFormed` is the same certificate carried across one spawn, and the
network it certifies holds a child: `the_newborn_has_a_permitted_parent` and
`the_newborn_generation_is_allocated` are read straight out of it, and neither is
a statement `quiet`'s certificate could make.

## What building it found

`Tests/Process/LifecycleStepFixtures.lean`'s `the_spawn` reaches
`Ending.holding newborn`, which is `quiet` with the slot filled — **and with
`quiet`'s empty nominal history**. So the spawned incarnation's generation is not
in the history, that world fails `NominalsAllocated`, and no `NetworkStep` wraps
that transition at all: `historyExact` cannot hold, because the transition
allocates a generation the world does not record.

`a_spawn_that_records_nothing_is_not_well_formed` states it. This is §10.87's
lesson in miniature and the reason `nominalsAllocated_preserved` is a law of
`NetworkStep`: a `Spawns` is a fact about instances, and only the *step* ties the
generation it hands out to the history that remembers it. A fixture can satisfy
every field of the former and still not be a step.

`spawned` is `holding newborn` with the history the spawn actually earned.
-/

namespace Grass.Process.Tests.Preservation

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Transition (serverPlan)
open Grass.Process.Tests.Ending (slot holding holding_slot)
open Grass.Process.Tests.LifecycleStep (newborn theGeneration)

/-! ## What a spawn that records nothing is -/

/--
**A spawn whose world does not record the generation reaches an ill-formed
network.**

`Spawns.allocatesTheGeneration` says the new incarnation's generation is in the
*allocation the step declares*. It does not say the world's history contains it,
and it cannot: a `LogicalProcessNetwork` and a `Spawns` between two of them know
nothing about `NetworkStep.historyExact`.
-/
theorem a_spawn_that_records_nothing_is_not_well_formed :
    ¬ (holding newborn).NominalsAllocated := by
  intro allocated
  have inHistory := allocated .connection slot newborn (holding_slot newborn)
  exact absurd inHistory (by
    show newborn.ref.generation ∉ (holding newborn).usedNominals.used
    exact List.not_mem_nil)

/-! ## The world a spawn actually reaches -/

/-- `holding newborn`, with the generation the spawn allocated recorded. -/
def spawned : ServerWorld :=
  { holding newborn with usedNominals := ⟨[⟨.processGeneration, 0⟩], by decide⟩ }

theorem spawned_slot : spawned.instances .connection slot = some newborn :=
  holding_slot newborn

/-- **A spawn that records what it allocated.** -/
theorem the_allocating_spawn :
    serverPlan.Spawns quiet spawned .connection slot theGeneration [] [] where
  wasEmpty := rfl
  nowLive := ⟨newborn, spawned_slot, trivial, rfl⟩
  spawnsAChild := by
    intro incarnation held
    rw [spawned_slot] at held
    cases held
    intro noParent
    cases noParent
  authorized := by
    intro incarnation held parentKind parent known
    rw [spawned_slot] at held
    cases held
    cases known
    exact ⟨rfl, rfl⟩
  allocatesTheGeneration := by
    intro incarnation held
    rw [spawned_slot] at held
    cases held
    exact List.mem_cons_self
  slotAgrees := by
    intro incarnation held
    rw [spawned_slot] at held
    cases held
    exact ⟨rfl, rfl⟩
  startsInitial := by
    intro incarnation held
    rw [spawned_slot] at held
    cases held
    exact ⟨rfl, rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := rfl
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind current =>
      cases kind with
      | listener => rfl
      | connection =>
        simp only [LogicalProcessNetworkCore.Agrees, spawned, holding,
          Tests.World.quiet]
        split
        · rename_i isSlot
          exact absurd (Or.inl (by rw [isSlot] :
            (Grass.Process.NetworkFragment.instanceState
              (topology := serverTopology) .connection current)
                = .instanceState .connection slot)) outside
        · rfl
    | nominals => exact absurd (Or.inr (Or.inl rfl)) outside
    | _ => rfl

/--
**And the step, which is what ties the generation to the history.**

`admissible` is law 22 — the identity was absent from the monotone history before
this step — and `historyExact` is §3's union equation. Neither is a field of the
transition, which is why `a_spawn_that_records_nothing_is_not_well_formed` is
possible at all.
-/
def theSpawnStep : serverPlan.NetworkStep quiet spawned where
  transition := .spawn .connection slot theGeneration [] [] the_allocating_spawn
  admissible := by
    intro nominal _
    exact List.not_mem_nil
  historyExact := rfl

/-! ## The capstone, applied -/

/--
**A well-formed network, obtained rather than asserted.**

Every clause of `quiet_is_wellFormed` is `absurd found`: the empty network is
well formed because there is nothing to be wrong about. This is that certificate
carried across a spawn, and the network it certifies holds a child.
-/
theorem spawned_is_wellFormed : spawned.WellFormed :=
  ProcessPlan.wellFormed_preserved theSpawnStep World.quiet_is_wellFormed

/--
And it says something. `quiet`'s certificate cannot state this theorem: there is
no incarnation to have a parent.
-/
theorem the_newborn_has_a_permitted_parent :
    serverTopology.maySpawn .listener .connection :=
  spawned_is_wellFormed.parentageValid .connection slot newborn spawned_slot
    .listener Instances.listenerZero rfl

/-- Nor this one, which is the clause with content at any plan. -/
theorem the_newborn_generation_is_allocated :
    newborn.ref.Allocated spawned.usedNominals :=
  spawned_is_wellFormed.nominalsAllocated .connection slot newborn spawned_slot

/-- Nor this: the slot and the incarnation in it agree. -/
theorem the_newborn_is_where_it_says :
    ∃ sameKind : newborn.kind = .connection,
      (sameKind ▸ newborn.ref.instanceId : serverTopology.InstanceId .connection) = slot :=
  spawned_is_wellFormed.slotsAgree .connection slot newborn spawned_slot

/-! ## Every transition in the corpus is a step

§10.89 suggests a cheap general check: for every `NetworkTransition` witness,
is there a `NetworkStep` wrapping it? A transition nothing can wrap is a
transition no execution contains, and every theorem stated over steps passes it
by. `the_spawn` failed that check.

The argument that the rest pass is one line — a non-allocating transition has
`allocatedNominals = Allocation.empty` definitionally, so `admissible` is vacuous
and `historyExact` reduces to "the history did not move", which holds at every
world built as `{quiet with …}`. This ledger's experience with one-line arguments
is what the rest of this section is for.
-/

open Grass.Process.Tests.Channel (wire)
open Grass.Process.Tests.Transition
  (payload occurrenceOf escrowed sent received the_send the_receive_after_the_send)

/-- The send is a step. -/
def theSendStep : serverPlan.NetworkStep quiet sent where
  transition := .send () payload occurrenceOf the_send
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- The receive after it is a step. -/
def theReceiveStep : serverPlan.NetworkStep sent received where
  transition := .receive () wire escrowed the_receive_after_the_send
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- And so is the reroute, which writes two ledgers. -/
def theRerouteStep :
    serverPlan.NetworkStep sent Grass.Process.Tests.Reroute.afterReroute where
  transition := .reroute () wire escrowed Grass.Process.Tests.Reroute.sidewire
    Grass.Process.Tests.Reroute.the_reroute
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/--
**And the send/receive pair carries well-formedness the whole way.**

`quiet` to `sent` to `received`, both steps, one certificate. The three channel
clauses are the ones with content across a delivery: `ReroutesLand` in
particular, since a delivery writes a resolution and `ResolvesNothingElse` is
what stops it writing more than one.
-/
theorem received_is_wellFormed : received.WellFormed :=
  ProcessPlan.wellFormed_preserved theReceiveStep
    (ProcessPlan.wellFormed_preserved theSendStep World.quiet_is_wellFormed)

/-- And the reroute's after-world is well formed, which is where the sixth clause
is the one doing work: the payload has to have landed somewhere. -/
theorem afterReroute_is_wellFormed : Grass.Process.Tests.Reroute.afterReroute.WellFormed :=
  ProcessPlan.wellFormed_preserved theRerouteStep
    (ProcessPlan.wellFormed_preserved theSendStep World.quiet_is_wellFormed)

/-- Read back out of it: the rerouted payload lands. -/
theorem the_rerouted_payload_lands :
    (Grass.Process.Tests.Reroute.afterReroute.inFlight () wire).ReroutedElsewhere
      (fun destination arrival =>
        arrival ∈ (Grass.Process.Tests.Reroute.afterReroute.inFlight () destination).created) :=
  afterReroute_is_wellFormed.reroutesLand () wire

end Grass.Process.Tests.Preservation
