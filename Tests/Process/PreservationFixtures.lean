import Grass.Process.Network.Initial
import Grass.Process.Network.WellFormedness
import Tests.Process.LifecycleStepFixtures
import Tests.Process.RerouteFixtures
import Tests.Process.CloseFixtures

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

/--
**And no step reaching that world can allocate the generation the spawn hands
out.**

The other half of the claim above, which a reviewer pointed out was prose.
`a_spawn_that_records_nothing_is_not_well_formed` shows the world is ill-formed;
this shows `NetworkStep.historyExact` cannot hold there, so the transition is not
merely a step to a bad world — it is not a step at all.
-/
theorem no_allocating_step_reaches_the_fixture_world
    (step : serverPlan.NetworkStep quiet (holding newborn))
    (allocates : (⟨.processGeneration, 0⟩ : LogicalNominal serverTopology.Carrier)
      ∈ step.transition.allocatedNominals.entries) : False := by
  have recorded := step.allocations_are_recorded allocates
  exact absurd recorded (by
    show (⟨.processGeneration, 0⟩ : LogicalNominal serverTopology.Carrier)
      ∉ (holding newborn).usedNominals.used
    exact List.not_mem_nil)

/-- And `the_spawn` allocates exactly that, so nothing wraps it. -/
theorem the_fixture_spawn_is_not_a_step
    (step : serverPlan.NetworkStep quiet (holding newborn))
    (isTheSpawn : step.transition.allocatedNominals = theGeneration) : False :=
  no_allocating_step_reaches_the_fixture_world step (by
    rw [isTheSpawn]
    exact List.mem_cons_self)

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

/--
**A start at the plan with channels and slots in it.**

Every field discharged at `withRoot`. What is *not* vacuous here and is at
`waitingPlan`: `nothingInFlight` and `sessionsFresh` quantify over a real edge
with a real `ChannelId` type rather than over `PEmpty`, `onlyTheRoot` has a
second role to exclude and an infinite slot type to exclude it at, and
`rootAllocated` is a membership in a one-element history rather than in an empty
one.
-/
def withRoot_is_a_start :
    serverPlan.ExactInitialNetwork ⟨0⟩ World.withRoot where
  rootSlot := ()
  root := World.rootListener
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
  rootAllocated := List.mem_cons_self
  onlyTheRoot := by
    intro kind slot incarnation found
    cases kind with
    | listener => exact ⟨rfl, rfl⟩
    | connection => exact absurd found (by intro equal; cases equal)
  nothingInFlight := fun _ _ => rfl
  sessionsFresh := fun _ _ => rfl
  sharedInvariantAtStart := by
    intro region
    cases region with
    | routeTable => exact List.nodup_nil
    | acceptCount => trivial
  historyFromEmpty :=
    NominalHistory.Reaches.extend (.refl _) LifecycleStep.theGeneration
      (by intro _ _; exact List.not_mem_nil)

/-- And a start is well formed, which at this plan says something about a real
instance rather than about an empty world. -/
theorem withRoot_is_wellFormed : World.withRoot.WellFormed :=
  withRoot_is_a_start.initial_is_wellformed


/-- The send is a step. -/
def theSendStep : serverPlan.NetworkStep World.withRoot sent where
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
    (ProcessPlan.wellFormed_preserved theSendStep withRoot_is_wellFormed)

/-- And the reroute's after-world is well formed, which is where the sixth clause
is the one doing work: the payload has to have landed somewhere. -/
theorem afterReroute_is_wellFormed : Grass.Process.Tests.Reroute.afterReroute.WellFormed :=
  ProcessPlan.wellFormed_preserved theRerouteStep
    (ProcessPlan.wellFormed_preserved theSendStep withRoot_is_wellFormed)

/-- The second send is a step. -/
def theSecondSendStep : serverPlan.NetworkStep sent Close.sent2 where
  transition := .send () payload Close.strandedOccurrence Close.the_second_send
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- And so is the close that ends both messages. -/
def theFullCloseStep : serverPlan.NetworkStep Close.sent2 Close.afterFullClose where
  transition := .channelClose () wire escrowed Close.the_full_close
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/--
**Three steps, one certificate**: `quiet` to `sent` to `sent2` to
`afterFullClose`.

The longest chain in the corpus, and the one where the escrow clauses do the most
work: two messages go in flight and both come out ended.
-/
theorem afterFullClose_is_wellFormed : Close.afterFullClose.WellFormed :=
  ProcessPlan.wellFormed_preserved theFullCloseStep
    (ProcessPlan.wellFormed_preserved theSecondSendStep
      (ProcessPlan.wellFormed_preserved theSendStep withRoot_is_wellFormed))

/--
**And the coalesce is a step too.**

§10.89's check, run against the transition §10.110 added. A reviewer pointed out
that `the_coalesce` landed in the same commit as the section stating that check
and was not put through it — a transition with no `NetworkStep` is the weaker
witness §10.89 warns about. §10.112.
-/
def theCoalesceStep : serverPlan.NetworkStep Close.sent2 Close.afterCoalesce where
  transition := .coalesce () wire [escrowed] Close.carrier Close.the_coalesce
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- And the two-source merge is a step too, which since §10.131 is one step
rather than two: `Coalesces` takes the whole family. -/
def theAtomicMergeStep : serverPlan.NetworkStep Close.sent2 Close.afterBothMerged where
  transition := .coalesce () wire [escrowed, Reroute.stranded] Close.carrier
    Close.the_atomic_merge
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

theorem afterBothMerged_is_wellFormed : Close.afterBothMerged.WellFormed :=
  ProcessPlan.wellFormed_preserved theAtomicMergeStep
    (ProcessPlan.wellFormed_preserved theSecondSendStep
      (ProcessPlan.wellFormed_preserved theSendStep withRoot_is_wellFormed))

/-- Two sends and a merge, carried from `quiet`. -/
theorem afterCoalesce_is_wellFormed : Close.afterCoalesce.WellFormed :=
  ProcessPlan.wellFormed_preserved theCoalesceStep
    (ProcessPlan.wellFormed_preserved theSecondSendStep
      (ProcessPlan.wellFormed_preserved theSendStep withRoot_is_wellFormed))

/-- And the carrier is on its own session, read out of the seventh clause. -/
theorem the_carrier_is_on_the_wire :
    Close.carrier.2.1 = wire :=
  afterCoalesce_is_wellFormed.occurrencesOnTheirSession () wire Close.carrier
    (by rw [Close.afterCoalesce_wire]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Read back out of it: the rerouted payload lands. -/
theorem the_rerouted_payload_lands :
    (Grass.Process.Tests.Reroute.afterReroute.inFlight () wire).ReroutedElsewhere
      (fun occurrence destination arrival =>
        arrival ∈ (Grass.Process.Tests.Reroute.afterReroute.inFlight () destination).created ∧
          arrival.1 = occurrence.1) :=
  afterReroute_is_wellFormed.reroutesLand () wire

/--
And the strong form, which the sixth clause no longer states and
`WellFormed.rerouted_arrival_is_on_its_destination` recovers from the seventh:
the arrival is on the session it was rerouted to. §10.112.
-/
theorem the_arrival_is_on_its_destination {occurrence destination}
    (rerouted : (Grass.Process.Tests.Reroute.afterReroute.inFlight () wire).resolution occurrence
      = some (.rerouted destination)) :
    ∃ arrival,
      arrival ∈ (Grass.Process.Tests.Reroute.afterReroute.inFlight () destination).created ∧
        arrival.1 = occurrence.1 ∧ arrival.2.1 = destination :=
  afterReroute_is_wellFormed.rerouted_arrival_is_on_its_destination () wire rerouted

/-! ## The rest of §10.89's check, run

The section above ran §10.89's check against the six constructors whose
transitions this branch had built at the time. A claims audit of the corpus found
eight more with a transition witness and no `NetworkStep` wrapping it: the two
session enders, the two endpoint deaths, the drop, the cancel request, and the
two instance endings. Each was the weaker witness §10.89 warns about — a
transition nothing can wrap is a transition no execution contains, and
`ProcessPlan.wellFormed_preserved` is stated over steps.

None of the eight was hard, and that is the point rather than a complaint: every
one of them is non-allocating, so `admissible` is vacuous and `historyExact` is
`rfl`. The check is cheap and it had simply not been run to the end.

Each step is paired with the well-formedness of the world it reaches, by the
capstone rather than by hand. That is the part that was actually missing: before
these, `afterClosing`, `afterDying`, `afterSenderDeath`, `afterReceiverDeath`,
`afterDropping`, `afterRequesting` and the two ending worlds were worlds no
theorem said anything about.
-/

open Grass.Process.Tests.ChannelStep
  (afterClosing afterDying afterDropping afterRequesting the_close the_death the_drop
   the_request)

/-- An ordinary close is a step. -/
def theCloseStep : serverPlan.NetworkStep sent afterClosing where
  transition := .channelClose () wire escrowed the_close
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- The world every one of these four starts from, named once. -/
theorem sent_is_wellFormed : sent.WellFormed :=
  ProcessPlan.wellFormed_preserved theSendStep withRoot_is_wellFormed

theorem afterClosing_is_wellFormed : afterClosing.WellFormed :=
  ProcessPlan.wellFormed_preserved theCloseStep sent_is_wellFormed

/-- And so is a channel death. -/
def theDeathStep : serverPlan.NetworkStep sent afterDying where
  transition := .channelDeath () wire escrowed the_death
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

theorem afterDying_is_wellFormed : afterDying.WellFormed :=
  ProcessPlan.wellFormed_preserved theDeathStep sent_is_wellFormed

/-- A drop is a step. -/
def theDropStep : serverPlan.NetworkStep sent afterDropping where
  transition := .drop () wire escrowed the_drop
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

theorem afterDropping_is_wellFormed : afterDropping.WellFormed :=
  ProcessPlan.wellFormed_preserved theDropStep sent_is_wellFormed

/-- And so is a cancellation request, which resolves nothing. -/
def theRequestStep : serverPlan.NetworkStep sent afterRequesting where
  transition := .requestCancel () wire escrowed the_request
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

theorem afterRequesting_is_wellFormed : afterRequesting.WellFormed :=
  ProcessPlan.wellFormed_preserved theRequestStep sent_is_wellFormed

/-! ### The four whose before-world is not `sent`

The two endpoint deaths and the two instance endings start from worlds built by
hand rather than reached by a step — a world holding a *dead* sender, or an
instance mid-countdown — so there is no chain from `quiet` to carry
well-formedness along. What §10.89's check asks for is still the step, and these
are it: each transition is one an execution can contain, which is the claim a
transition alone does not make.

That the before-worlds are unreached is worth saying rather than leaving
implicit. It is the same distinction §10.88 drew between inhabited and exercised,
one level down: a step from an unreachable world is a real step, and it is not a
step of any run.

**§10.132 ran that down and got the answer wrong the first time.** The first
version of this section gave three of the four a step into their before-world
and said they were therefore reachable. A fresh reviewer refuted it: each new
predecessor world has an *empty root slot*, so none of them is a world of a run
either, and the gap had moved back exactly one step rather than closing.

What closes it is an invariant over executions rather than steps.
`ProcessPlan.execution_holds_an_unkilled_root` says every world of every run
holds, in the root's slot, an instance with no current parent that has not died —
unless a `restart` at that slot took it away, which
`no_restart_at_the_root_slot` shows is unconstructible here. So none of the seven
worlds below is a world of any run. Four theorems cover them: three name a world
each and the fourth is quantified over every `holding` world. §10.133.
-/

open Grass.Process.Tests.ChannelStep
  (sentWithDeadSender afterSenderDeath sentWithDeadReceiver afterReceiverDeath
   the_sender_death the_receiver_death deadConnection sentWithDeadReceiver_slot)
open Grass.Process.Tests.Ending (holding settling waitingOnATick
  an_honest_termination an_honest_interruption)
open Grass.Process.Tests.Instances (finished counting)

/-- A sender's death is a step. -/
def theSenderDeathStep : serverPlan.NetworkStep sentWithDeadSender afterSenderDeath where
  transition := .senderDeath () wire escrowed .supervised the_sender_death
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- And a receiver's. -/
def theReceiverDeathStep :
    serverPlan.NetworkStep sentWithDeadReceiver afterReceiverDeath where
  transition := .receiverDeath () wire escrowed .providerLost the_receiver_death
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- A termination is a step. -/
def theTerminationStep :
    serverPlan.NetworkStep (holding settling) (holding finished) where
  transition := .processTermination Role.connection Ending.slot ⟨()⟩ (fun _ _ _ => True)
    an_honest_termination
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- And so is an interruption of the demand the instance is holding. -/
def theInterruptionStep (reason : Interrupt) :
    serverPlan.NetworkStep (holding waitingOnATick)
      (holding { waitingOnATick with lifecycle := .interrupted Demand.tick reason }) where
  transition := .interrupt Role.connection Ending.slot Demand.tick reason
    (fun _ _ _ => True) (an_honest_interruption reason)
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl


/-! ### And which of the four before-worlds a step can reach

§10.129 left "reaching those before-worlds by steps is owed" and guessed the job
was four `processStep`s. Three of the four, near enough; the fourth is a theorem
in the other direction. §10.132.
-/

/-- The wire's receiver before it died: the same incarnation, running. -/
def liveConnection : ProcessInstance serverTopology :=
  { deadConnection with lifecycle := .running }

/-- The sent world with that receiver alive, which is `sentWithDeadReceiver` one
step earlier. -/
noncomputable def sentWithLiveReceiver : ServerWorld :=
  { sent with
      instances := fun kind current =>
        match kind, current with
        | .listener, _ => none
        | .connection, n => if n = 7 then some liveConnection else none }

theorem sentWithLiveReceiver_slot :
    sentWithLiveReceiver.instances .connection wire.receiver.instanceId
      = some liveConnection := rfl

/--
**The receiver's death is earned by a step**, so `theReceiverDeathStep`'s
before-world is one the *family* admits a step into.

`childDied` is the only constructor that writes `.died`, and it carries
`wasChild` — which `liveConnection` records, being `.attached .listener`. That is
what separates this case from the sender's below, where no constructor can write
the death at all.

**It is not a world of a run**, and the distinction is the whole of §10.133:
`sentWithDeadReceiver_is_no_world_of_a_run` and
`no_run_reaches_sentWithDeadReceiver` below say so, and `sentWithLiveReceiver`
is no better — both have an empty root slot.
-/
theorem the_receiver_is_killed :
    serverPlan.EndsInstance sentWithLiveReceiver sentWithDeadReceiver .connection
      wire.receiver.instanceId (.died .providerLost) (fun _ _ _ => True) where
  notRunning := by intro equal; cases equal
  wasLive := ⟨liveConnection, sentWithLiveReceiver_slot, trivial⟩
  nowEnded := ⟨deadConnection, sentWithDeadReceiver_slot, rfl, rfl⟩
  identityPreserved :=
    ⟨liveConnection, deadConnection, rfl, rfl, sentWithLiveReceiver_slot,
      sentWithDeadReceiver_slot, rfl, rfl, rfl, rfl⟩
  endingIsEarned := by
    refine ⟨liveConnection, rfl, sentWithLiveReceiver_slot, ?_, ?_⟩
    · intro result isTerminated
      exact absurd isTerminated (by intro equal; cases equal)
    · intro demand reason isInterrupted
      exact absurd isInterrupted (by intro equal; cases equal)
  custodyDeclared :=
    ⟨liveConnection, sentWithLiveReceiver_slot, rfl, trivial, fun other _ => by cases other; rfl⟩
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind current =>
      cases kind with
      | listener => rfl
      | connection =>
        show sentWithLiveReceiver.instances .connection current
          = sentWithDeadReceiver.instances .connection current
        simp only [sentWithLiveReceiver, sentWithDeadReceiver]
        split
        · rename_i isSeven
          exact absurd (Or.inl (by rw [isSeven]; rfl)) outside
        · rfl
    | _ => rfl

/-- And it *records* a current parent, which is what `childDied` asks and what the
sender below cannot supply. Note what it does not show: `sentWithLiveReceiver`
holds no listener at all, so the parent this instance names is not in the world.
`wasChild` checks that a supervisor is recorded;
`LogicalProcessNetworkCore.ParentageValid` is what checks the record. -/
theorem the_live_receiver_is_a_child : ∀ incarnation,
    sentWithLiveReceiver.instances .connection wire.receiver.instanceId = some incarnation →
    incarnation.parentage.currentParent ≠ none := by
  intro incarnation found
  rw [sentWithLiveReceiver_slot] at found
  injection found with same
  rw [← same]
  intro empty
  cases empty

/-- And it is a step, so the *family* admits one into `sentWithDeadReceiver`.

Not a run: `no_run_reaches_sentWithDeadReceiver` below. A third reviewer found
this sentence still claiming the opposite after the commit that reported fixing
it had fixed its two neighbours and missed this one — which is §10.135. -/
def theReceiverIsKilledStep :
    serverPlan.NetworkStep sentWithLiveReceiver sentWithDeadReceiver where
  transition := .childDied .connection wire.receiver.instanceId .providerLost
    (fun _ _ _ => True) the_live_receiver_is_a_child the_receiver_is_killed
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-! #### And none of these worlds is a world of a run

The correction §10.133 records. A step into a world says the transition is one an
execution can *contain*; it does not say the execution reaches the world, and the
first version of this section conflated the two.
-/

/--
**No restart can happen at the listener's slot**, which is what discharges
`execution_holds_an_unkilled_root`'s one escape at this plan.

`Restarts.restartsAChild` requires the new incarnation to have a current parent
and `Restarts.authorized` requires that parent to be one
`ProcessGraph.maySpawn` permits. `serverTopology.maySpawn` is
`fun parent child => parent = .listener ∧ child = .connection`, so no parent may
spawn a listener and the two fields cannot both hold. §10.133's second half — the
gap where a restart deletes the root — is real at the family and unreachable
here, and this is the proof of the second clause rather than an assumption of it.
-/
theorem no_restart_at_the_root_slot {before after : ServerWorld}
    {allocation : Allocation serverTopology.Carrier}
    {emitted : Trace fixtureBoundary.Observation}
    {localEmitted : ObservationSegment (serverTopology.protocol .listener).Observation}
    (step : serverPlan.Restarts before after .listener () allocation emitted localEmitted) :
    False := by
  obtain ⟨incarnation, found, _, _⟩ := step.nowLive
  obtain ⟨isKind, _⟩ := step.slotAgrees incarnation found
  have hasParent := step.restartsAChild incarnation found
  obtain ⟨parentKind, parent, known⟩ :=
    ProcessParentage.knownParent_of_currentParent incarnation.parentage hasParent
  have permitted := step.authorized incarnation found parentKind parent known
  rw [isKind] at permitted
  exact absurd permitted.2 (by intro equal; cases equal)

/--
**So every run of `serverPlan` ends holding an unkilled root.**

`ProcessPlan.execution_holds_an_unkilled_root` with its restart escape closed.
The four `no_run_reaches_*` corollaries below apply it. The five
`*_is_no_world_of_a_run` theorems do not — they are read off `UnkilledRootAt`
directly and would stand without this theorem; it is what turns them into
statements about executions. That is §10.129's actual question: not a step into
each before-world, but a reason no execution is ever in one.
-/
theorem every_run_holds_an_unkilled_root
    {request : (serverTopology.protocol serverTopology.root).Request}
    {start final : ServerWorld} (isStart : serverPlan.ExactInitialNetwork request start)
    (execution : serverPlan.StepsTo start final) :
    serverPlan.UnkilledRootAt final .listener () :=
  serverPlan.execution_holds_an_unkilled_root execution
    isStart.initial_is_wellformed
    (ProcessPlan.start_holds_an_unkilled_root isStart)
    (fun _ _ _ _ _ restart => no_restart_at_the_root_slot restart)

/--
**And `sentWithDeadSender` is not one**, which is the fourth of §10.129's four.

It holds `World.rootListener` — parentage `.root`, so no current parent — in the
`.died` state, and `UnkilledRootAt`'s death clause is exactly what that fails —
its first two, an instance in the slot with no current parent, both hold. `theSenderDeathStep` is a real step and it is a step of no run. That is
§10.88's inhabited-versus-exercised distinction, and unlike the first version of
this section it is now proved rather than asserted.
-/
theorem sentWithDeadSender_is_no_world_of_a_run :
    ¬ serverPlan.UnkilledRootAt sentWithDeadSender .listener () := by
  rintro ⟨root, found, _, unkilled⟩
  injection found with same
  subst same
  exact unkilled .supervised rfl

/-- **And neither is the world the receiver's death is reached from**, nor the
one it reaches: both have an empty root slot, `sent` notwithstanding. -/
theorem sentWithLiveReceiver_is_no_world_of_a_run :
    ¬ serverPlan.UnkilledRootAt sentWithLiveReceiver .listener () := by
  rintro ⟨_, found, _⟩
  exact absurd found (by intro equal; cases equal)

theorem sentWithDeadReceiver_is_no_world_of_a_run :
    ¬ serverPlan.UnkilledRootAt sentWithDeadReceiver .listener () := by
  rintro ⟨_, found, _⟩
  exact absurd found (by intro equal; cases equal)

/-- **Nor any `holding` world**, which covers the two instance endings and the
two worlds their steps start from. `Ending.holding` maps the listener to `none`
by construction. -/
theorem holding_is_no_world_of_a_run (incarnation : ProcessInstance serverTopology) :
    ¬ serverPlan.UnkilledRootAt (holding incarnation) .listener () := by
  rintro ⟨_, found, _⟩
  exact absurd found (by intro equal; cases equal)

/-! ##### And the same three, as statements about runs rather than about worlds

Local adversarial review's second round pointed out that `¬ UnkilledRootAt w` is
one inference away from "no run reaches `w`" and that leaving the inference to
the reader is how the first version's prose went wrong. These are the inference,
written down.
-/

theorem no_run_reaches_sentWithDeadSender
    {request : (serverTopology.protocol serverTopology.root).Request} {start : ServerWorld}
    (isStart : serverPlan.ExactInitialNetwork request start)
    (execution : serverPlan.StepsTo start sentWithDeadSender) : False :=
  sentWithDeadSender_is_no_world_of_a_run
    (every_run_holds_an_unkilled_root isStart execution)

theorem no_run_reaches_sentWithDeadReceiver
    {request : (serverTopology.protocol serverTopology.root).Request} {start : ServerWorld}
    (isStart : serverPlan.ExactInitialNetwork request start)
    (execution : serverPlan.StepsTo start sentWithDeadReceiver) : False :=
  sentWithDeadReceiver_is_no_world_of_a_run
    (every_run_holds_an_unkilled_root isStart execution)

theorem no_run_reaches_a_holding_world (incarnation : ProcessInstance serverTopology)
    {request : (serverTopology.protocol serverTopology.root).Request} {start : ServerWorld}
    (isStart : serverPlan.ExactInitialNetwork request start)
    (execution : serverPlan.StepsTo start (holding incarnation)) : False :=
  holding_is_no_world_of_a_run incarnation
    (every_run_holds_an_unkilled_root isStart execution)

/-- And the world the corpus does reach really does hold an unkilled root, so
the invariant above is not vacuous. -/
theorem sent_holds_an_unkilled_root : serverPlan.UnkilledRootAt sent .listener () :=
  ⟨World.rootListener, rfl, rfl, fun _ dead => by cases dead⟩



/-! #### And a role that may write nothing owes nothing

`NetworkTransition.sharedWritesAdmitted_of_no_writes` was cited by two docstrings
and declared by neither until §10.136. Declaring it is only half the repair: a
lemma with no consumer and an unsatisfiable hypothesis would be the shape this
ledger refuses. Both halves are here.
-/

/-- **`serverTopology`'s connection role may write no region.**

`sharedAccess .connection .routeTable` is `.readOnly` and
`sharedAccess .connection .acceptCount` is `.none`, and `mayWrite` is `false` in
both — so the hypothesis of `sharedWritesAdmitted_of_no_writes` is satisfiable at
a real role of a real plan rather than only in principle. The listener is the
contrast: it may write `.acceptCount`, which is what
`Tests/Process/ProcessStepFixtures.lean`'s `the_listener_counts` spends. -/
theorem the_connection_writes_nothing (region : serverTopology.SharedRegion) :
    (serverTopology.sharedAccess .connection region).mayWrite = false := by
  cases region <;> rfl

/-- And the consumer: at that role, `sharedWritesAdmitted` follows from
`writesPermitted` with no argument about values at all. -/
theorem theConnectionOwesNoValueBound {before after : ServerWorld}
    {slot : serverTopology.InstanceId Role.connection}
    {event : (serverTopology.protocol Role.connection).Event}
    {issued : Bag (serverTopology.protocol Role.connection).Demand}
    {localEmitted : ObservationSegment (serverTopology.protocol Role.connection).Observation}
    (permitted : ∀ region, before.shared region ≠ after.shared region →
      (serverTopology.sharedAccess Role.connection region).mayWrite = true) :
    ∀ region, before.shared region ≠ after.shared region →
      ∀ (fromInstance toInstance : ProcessInstance serverTopology)
        (fromKind : fromInstance.kind = Role.connection)
        (toKind : toInstance.kind = Role.connection),
        before.instances Role.connection slot = some fromInstance →
        after.instances Role.connection slot = some toInstance →
        serverPlan.sharedUpdate Role.connection event (fromKind ▸ fromInstance.localState)
          (toKind ▸ toInstance.localState) issued localEmitted region
          (before.shared region) (after.shared region) :=
  ProcessPlan.sharedWritesAdmitted_of_no_writes (plan := serverPlan)
    (before := before) (after := after) (slot := slot) (event := event) (issued := issued)
    (localEmitted := localEmitted) the_connection_writes_nothing permitted

/-! #### And a dead instance with no parent, which a detach reaches

The refutation §10.133 records. `NetworkTransition.dying_was_supervised` says a
step that *kills* an instance found it with a current parent, and it is easy to
read that as "a dead instance has a current parent". That reading is false, and
the counterexample is one step from the world above: `Detaches` has no liveness
requirement — `wasAttached` asks only for a current parent — and
`identityPreserved` *pins* the lifecycle across the step. So a dead child
detaches into a dead orphan, and nothing was killed in the process.

The gap this is a witness for is not in `dying_was_supervised`. It is the
question of whether a supervisor should be able to let go of a corpse at all,
which `agent-bus` `c-process:103` asks `g-design` and which is why this fixture
exists rather than a new field on `Detaches`.
-/

/-- The wire's receiver: dead, and then let go. -/
def orphanedDeadConnection : ProcessInstance serverTopology :=
  { deadConnection with parentage := .detached .listener Instances.listenerZero }

theorem orphanedDeadConnection_is_dead :
    orphanedDeadConnection.lifecycle = .died .providerLost := rfl

/-- **And it has no current parent** — exactly the state `dying_was_supervised`
refuses a *killing* step to produce. -/
theorem orphanedDeadConnection_has_no_parent :
    orphanedDeadConnection.parentage.currentParent = none := rfl

noncomputable def deadOrphanWorld : ServerWorld :=
  { sent with
      instances := fun kind current =>
        match kind, current with
        | .listener, _ => none
        | .connection, n => if n = 7 then some orphanedDeadConnection else none }

theorem deadOrphanWorld_slot :
    deadOrphanWorld.instances .connection wire.receiver.instanceId
      = some orphanedDeadConnection := rfl

/-- **A detach of a corpse is a legal `Detaches`.** -/
theorem a_corpse_may_be_orphaned :
    serverPlan.Detaches sentWithDeadReceiver deadOrphanWorld .connection
      wire.receiver.instanceId where
  wasAttached := ⟨deadConnection, sentWithDeadReceiver_slot, by intro empty; cases empty⟩
  identityPreserved :=
    ⟨deadConnection, orphanedDeadConnection, rfl, rfl, sentWithDeadReceiver_slot,
      deadOrphanWorld_slot, rfl, rfl, rfl, rfl, rfl, rfl⟩
  onlyThatSlot :=
    { scope := by
        intro fragment outside
        cases fragment with
        | instanceState kind current =>
          cases kind with
          | listener => rfl
          | connection =>
            show sentWithDeadReceiver.instances .connection current
              = deadOrphanWorld.instances .connection current
            simp only [sentWithDeadReceiver, deadOrphanWorld]
            split
            · rename_i isSeven
              exact absurd (by rw [isSeven]; rfl) outside
            · rfl
        | _ => rfl }

/-- And it is a step, so the dead orphan is two steps from a world holding a
live attached child — `theReceiverIsKilledStep`, then this. -/
def theOrphaningStep : serverPlan.NetworkStep sentWithDeadReceiver deadOrphanWorld where
  transition := .detach .connection wire.receiver.instanceId a_corpse_may_be_orphaned
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

theorem deadOrphanWorld_is_no_world_of_a_run :
    ¬ serverPlan.UnkilledRootAt deadOrphanWorld .listener () := by
  rintro ⟨_, found, _⟩
  exact absurd found (by intro equal; cases equal)

/-- **And no run reaches this particular dead-orphan world**, which is the
sentence `NetworkTransition.dying_was_supervised`'s docstring used to assert
without a declaration behind it.

Read what it proves and not more. `deadOrphanWorld`'s *listener* slot is empty,
and that is the whole proof; nothing here says a run cannot reach some other
world holding a dead orphan at a connection slot with the root intact. Nor is
"a world of no run" this file's norm — `World.withRoot` is a start,
`theSendStep` reaches `sent` from it, and `sent_holds_an_unkilled_root` is above.
§10.136. -/
theorem no_run_reaches_deadOrphanWorld
    {request : (serverTopology.protocol serverTopology.root).Request} {start : ServerWorld}
    (isStart : serverPlan.ExactInitialNetwork request start)
    (execution : serverPlan.StepsTo start deadOrphanWorld) : False :=
  deadOrphanWorld_is_no_world_of_a_run
    (every_run_holds_an_unkilled_root isStart execution)

/-! #### And the two instance endings

Both before-worlds are `holding` an incarnation of the connection, and both are
one `processStep` from another such world. Neither step emits, which is what
makes the after-world `holding` something rather than `holding` something with a
`beep` on its pending trace — `countdown`'s only emitting event is a settled
`tick`, and neither of these is one.
-/

/-- The connection holding a `log` it has not answered. -/
def countingOnALog : ProcessInstance serverTopology :=
  { counting with outstanding := Bag.ofList [Demand.log] }

/--
**Answering the `log` issues the `tick`**, and reaches `waitingOnATick` exactly.

`countdown`'s `log` case is the one that "consumes one occurrence and issues
another" — `Tests/Process/M1Fixtures.lean` says so — so the outstanding bag ends
holding a `tick` the instance really issued rather than one a fixture wrote down.
That is what `an_honest_interruption`'s before-world needed and did not have.
-/
theorem the_log_is_answered (answer : countdownVocabulary.Result .log) :
    serverPlan.StepsLocally (holding countingOnALog) (holding waitingOnATick) .connection slot
      (.result .log answer) [] (Bag.ofList [Demand.tick]) [] where
  from' := ⟨countingOnALog, holding_slot countingOnALog, trivial, rfl⟩
  stillLive := ⟨waitingOnATick, holding_slot waitingOnATick, trivial⟩
  protocolStep :=
    ⟨countingOnALog, waitingOnATick, rfl, rfl, holding_slot countingOnALog,
      holding_slot waitingOnATick, ⟨by decide, rfl, rfl, rfl⟩, ⟨0, rfl, rfl⟩, rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := rfl
  writesPermitted := by
    intro region moved
    exact absurd rfl moved
  sharedWritesAdmitted := by
    intro region moved
    exact absurd rfl moved
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind current =>
      cases kind with
      | listener => rfl
      | connection =>
        simp only [LogicalProcessNetworkCore.Agrees, holding]
        split
        · rename_i isSlot
          exact absurd (Or.inl (by rw [isSlot])) outside
        · rfl
    | _ => rfl

/-- So `an_honest_interruption`'s before-world is one the family admits a step
into. It is not a world of a run — `holding` maps the listener to `none`, and
`holding_is_no_world_of_a_run` covers every `holding` world including this one. -/
def theLogStep (answer : countdownVocabulary.Result .log) :
    serverPlan.NetworkStep (holding countingOnALog) (holding waitingOnATick) where
  transition := .processStep .connection slot (.result .log answer) []
    (Bag.ofList [Demand.tick]) [] (the_log_is_answered answer)
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-- The connection one tick from the end, holding that tick. -/
def oneToGo : ProcessInstance serverTopology :=
  { counting with localState := ⟨1⟩, outstanding := Bag.ofList [Demand.tick] }

/--
**And abandoning that last tick reaches `settling`.**

`countdown`'s `.interrupted` case decrements and emits nothing, so this lands on
state zero — the state `countdown.Terminal` calls finished, which is exactly what
`an_honest_termination` reads off its before-world.

The event is an interruption *of the run relation* and not a
`NetworkTransition.interrupt`: the instance handles it and stays running, which
is why this is a `processStep`. A settled `tick` would reach the same state and
emit a `beep`, so the after-world would be `holding settling` with a pending
trace and not `holding settling`; the interruption is the event that reaches this
world on the nose.
-/
theorem the_last_tick_is_abandoned (reason : Interrupt) :
    serverPlan.StepsLocally (holding oneToGo) (holding settling) .connection slot
      (.interrupted Demand.tick reason) [] 0 [] where
  from' := ⟨oneToGo, holding_slot oneToGo, trivial, rfl⟩
  stillLive := ⟨settling, holding_slot settling, trivial⟩
  protocolStep :=
    ⟨oneToGo, settling, rfl, rfl, holding_slot oneToGo, holding_slot settling,
      ⟨by decide, rfl, rfl, rfl⟩, ⟨0, rfl, rfl⟩, rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := rfl
  writesPermitted := by
    intro region moved
    exact absurd rfl moved
  sharedWritesAdmitted := by
    intro region moved
    exact absurd rfl moved
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind current =>
      cases kind with
      | listener => rfl
      | connection =>
        simp only [LogicalProcessNetworkCore.Agrees, holding]
        split
        · rename_i isSlot
          exact absurd (Or.inl (by rw [isSlot])) outside
        · rfl
    | _ => rfl

/-- So `an_honest_termination`'s before-world is one too, and equally not a world
of a run, for the same reason. -/
def theLastTickStep (reason : Interrupt) :
    serverPlan.NetworkStep (holding oneToGo) (holding settling) where
  transition := .processStep .connection slot (.interrupted Demand.tick reason) [] 0 []
    (the_last_tick_is_abandoned reason)
  admissible := by intro _ nothing; cases nothing
  historyExact := rfl

/-! ## And a start at a plan with something in it

§10.88: `ExactInitialNetwork` had one witness in the corpus,
`Tests/Process/FrontierFixtures.lean`'s `waiting_is_a_start`, at a plan whose
demand, observation, fault, violation, terminal-result, region and channel types
are all `PEmpty` and whose kinds and slots are all `Unit`. Fifteen of its sixteen
fields are `rfl`, `trivial` or `.elim`.

`serverPlan` is the other fixture plan: two roles, a channel edge, a real
observation type, `Nat`-indexed connection slots and a shared region. It had no
start. `Tests/Process/WorldFixtures.lean`'s `withRoot` is one — a listener
holding the root parentage, its generation allocated — and nothing had said so.
-/

/--
And sound, which at this plan is the same claim under another name — §10.82.

Worth stating anyway: `terminated_result_is_exact` takes a `Sound`, and until
`waiting_is_sound` nothing had ever supplied one. This is the second, at a plan
whose terminal-result type is not empty.
-/
theorem withRoot_is_sound : serverPlan.Sound World.withRoot :=
  ⟨withRoot_is_wellFormed⟩

/-- And so is the world one spawn later, by the capstone rather than by hand. -/
theorem spawned_is_sound : serverPlan.Sound spawned :=
  ⟨spawned_is_wellFormed⟩

end Grass.Process.Tests.Preservation
