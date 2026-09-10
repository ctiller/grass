import Tests.Process.PreservationFixtures
import Tests.Process.EscrowReceiveUpdate

/-! A fully initialized spawn-send-receive path for the atomic channel receive.
The original `wire` deliberately aliases the root's generation; `freshWire`
uses a distinct receiver generation so its child can actually be spawned. -/

namespace Grass.Process.Tests.InitializedReceive

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld withRoot)
open Grass.Process.Tests.Channel
open Grass.Process.Tests.EscrowReceiveUpdate

noncomputable section
open Classical

def freshWire : serverTopology.ChannelId () where
  sender := Instances.listenerZero
  receiver := connectionSeven 1
  epoch := ⟨.channelEpoch, 1⟩
  isEpoch := rfl

@[reducible] def freshSteps := liveStepsAt freshWire

@[reducible] noncomputable def freshPlan :
    ProcessPlan graphRegistry fixtureBoundary World.NoObligations :=
  { Transition.serverPlan with
      topology := serverTopology
      message := World.serverMessage
      steps := fun _ => freshSteps
      channel := fun _ => liveChannelAt freshWire }

def initial : freshPlan.ExactInitialNetwork ⟨0⟩ withRoot where
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

def receiver : ProcessInstance serverTopology where
  kind := .connection
  ref := connectionSeven 1
  parentage := .attached .listener Instances.listenerZero
  request := ⟨3⟩
  localState := ⟨3⟩
  outstanding := Bag.ofList [Demand.tick, Demand.tick, Demand.tick]
  lifecycle := .running

def receiverGeneration : Allocation serverTopology.Carrier where
  entries := [⟨.processGeneration, 1⟩]
  distinct := by decide

@[reducible] def receiverSlot : serverTopology.InstanceId .connection := 7

def spawned : ServerWorld :=
  { withRoot with
      instances := fun kind slot =>
        match kind with
        | .listener => some World.rootListener
        | .connection => if slot = receiverSlot then some receiver else none
      usedNominals := ⟨[⟨.processGeneration, 1⟩, ⟨.processGeneration, 0⟩], by decide⟩ }

@[simp] theorem spawned_inFlight (session : serverTopology.ChannelId ()) :
    spawned.inFlight () session = EscrowLedger.empty := rfl

@[simp] theorem spawned_receiver :
    spawned.instances .connection freshWire.receiver.instanceId = some receiver := by
  simp [spawned, freshWire, connectionSeven, receiverSlot]

@[simp] theorem spawned_slot :
    spawned.instances .connection receiverSlot = some receiver := by
  simp [spawned, receiverSlot]

theorem the_spawn :
    freshPlan.Spawns withRoot spawned .connection receiverSlot receiverGeneration [] [] where
  wasEmpty := rfl
  nowLive := ⟨receiver, spawned_receiver, trivial, rfl⟩
  spawnsAChild := by
    intro incarnation found
    rw [spawned_slot] at found
    cases found
    intro noParent
    cases noParent
  authorized := by
    intro incarnation found parentKind parent known
    rw [spawned_slot] at found
    cases found
    simp [receiver] at known
    rcases known with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  allocatesTheGeneration := by
    intro incarnation found
    rw [spawned_slot] at found
    cases found
    exact List.mem_cons_self
  slotAgrees := by
    intro incarnation found
    rw [spawned_slot] at found
    cases found
    exact ⟨rfl, rfl⟩
  startsInitial := by
    intro incarnation found
    rw [spawned_slot] at found
    cases found
    exact ⟨rfl, rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := rfl
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind slot =>
      cases kind with
      | listener => rfl
      | connection =>
        simp only [LogicalProcessNetworkCore.Agrees, spawned, withRoot]
        split
        · rename_i same
          exact absurd (Or.inl (by subst same; rfl)) outside
        · rfl
    | nominals => exact absurd (Or.inr (Or.inl rfl)) outside
    | _ => rfl

def spawnStep : freshPlan.NetworkStep withRoot spawned where
  transition := .spawn .connection receiverSlot receiverGeneration [] [] the_spawn
  admissible := by
    intro nominal held
    change nominal ∈ receiverGeneration.entries at held
    rw [show nominal = ⟨.processGeneration, 1⟩ by simpa [receiverGeneration] using held]
    intro inHistory
    simp only [withRoot, List.mem_singleton] at inHistory
    have carriers := congrArg LogicalNominal.carrier inHistory
    exact Nat.one_ne_zero carriers
  historyExact := rfl

def payload : ServerMessage := ⟨9⟩

def occurrence : serverTopology.ChannelOccurrence () payload :=
  ⟨freshWire, { id := ⟨.messageOccurrence, 1⟩, isMessage := rfl }⟩

@[simp] theorem occurrence_session : occurrence.1 = freshWire := rfl

def escrowed : EdgeOccurrence serverTopology World.serverMessage () := ⟨payload, occurrence⟩

noncomputable def sent : ServerWorld :=
  { spawned with inFlight := fun _ session =>
      if session = freshWire then Channel.holding escrowed else spawned.inFlight () session }

@[simp] theorem sent_freshWire : sent.inFlight () freshWire = Channel.holding escrowed := by
  simp [sent]

theorem the_send : freshPlan.SendsEscrow spawned sent () payload occurrence where
  senderIsLive := ⟨World.rootListener, rfl, ⟨rfl, rfl⟩, trivial⟩
  contractual := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · change escrowed ∉ (spawned.inFlight () freshWire).created
      simp [EscrowLedger.empty]
    · change (sent.inFlight () freshWire).Outstanding escrowed
      rw [sent_freshWire]
      exact ⟨List.mem_cons_self, rfl⟩
  identityIsFresh := by
    intro other held
    rw [occurrence_session, spawned_inFlight] at held
    exact absurd held List.not_mem_nil
  nowEscrowed := by
    change (sent.inFlight () freshWire).Outstanding escrowed
    rw [sent_freshWire]
    exact ⟨List.mem_cons_self, rfl⟩
  resolvesNothing := by
    intro other
    change (sent.inFlight () freshWire).resolution other =
      (spawned.inFlight () freshWire).resolution other
    simp [sent, Channel.holding, EscrowLedger.empty]
  requestsNothing := by
    intro other
    change (sent.inFlight () freshWire).cancelRequested other =
      (spawned.inFlight () freshWire).cancelRequested other
    simp [sent, Channel.holding, EscrowLedger.empty]
  createsOnlyTheMessage := by
    intro other held absent
    rw [occurrence_session] at held absent
    rw [sent_freshWire] at held
    exact List.mem_singleton.mp held
  ledgerExtends := by
    refine ⟨List.nil_prefix, ?_, ?_⟩
    · intro other resolution ended
      exact absurd ended (by simp [EscrowLedger.empty])
    · intro other requested
      exact absurd requested (by simp [EscrowLedger.empty])
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      by_cases same : session = freshWire
      · subst same
        exact (outside rfl).elim
      · simp [LogicalProcessNetworkCore.Agrees, sent, same]
    | _ => rfl

def sendStep : freshPlan.NetworkStep spawned sent where
  transition := .send () payload occurrence the_send
  admissible := by intro _ held; cases held
  historyExact := rfl

noncomputable def received : ServerWorld :=
  let outstanding : (sent.inFlight () freshWire).Outstanding escrowed := by
    rw [sent_freshWire]
    exact ⟨List.mem_cons_self, rfl⟩
  { sent with
      inFlight := fun _ session =>
        if session = freshWire then receiveUpdate (sent.inFlight () freshWire) escrowed outstanding
        else sent.inFlight () session
      sessions := fun _ session =>
        if session = freshWire then
          { sent.sessions () freshWire with delivered := (sent.sessions () freshWire).delivered + 1 }
        else sent.sessions () session }

theorem the_receive : freshPlan.Delivers sent received () freshWire escrowed [] 0 [] := by
  let outstanding : (sent.inFlight () freshWire).Outstanding escrowed := by
    rw [sent_freshWire]
    exact ⟨List.mem_cons_self, rfl⟩
  refine
    { contractual := ⟨rfl, outstanding, rfl, by simp [received]⟩
      onItsSession := rfl
      wasOutstanding := outstanding
      nowResolved := by simp [received]
      ledgerExtends := by simpa [received] using
        receiveUpdate_extends (sent.inFlight () freshWire) escrowed outstanding
      resolvesNothingElse := by simpa [received] using
        receiveUpdate_resolves_nothing_else (sent.inFlight () freshWire) escrowed outstanding
      createsNothing := by simpa [received] using
        receiveUpdate_creates_nothing (sent.inFlight () freshWire) escrowed outstanding
      requestsNothing := by simpa [received] using
        receiveUpdate_requests_nothing (sent.inFlight () freshWire) escrowed outstanding
      cursorAdvances := by simp [received]
      statusUnchanged := by simp [received]
      receiverStep := ?_
      receiverRef := ?_
      scope := ?_ }
  · refine
      { from' := ⟨receiver, by simp [sent, spawned, freshWire, connectionSeven], trivial, rfl⟩
        stillLive := ⟨receiver, by simp [received, sent, spawned, freshWire, connectionSeven], trivial⟩
        protocolStep := ?_
        emittedIsProjected := rfl
        producesPending := rfl
        writesPermitted := by intro region moved; exact absurd rfl moved
        sharedWritesAdmitted := by intro region moved; exact absurd rfl moved }
    refine ⟨receiver, receiver, rfl, rfl, by simp [sent, spawned, freshWire, connectionSeven],
      by simp [received, sent, spawned, freshWire, connectionSeven], ?_, ?_, rfl, rfl, rfl⟩
    · exact ⟨by decide, rfl, rfl, rfl⟩
    · change receiver.outstanding = receiver.outstanding + 0
      simp
  · intro incarnation found
    simp [sent, spawned, freshWire, connectionSeven] at found
    cases found
    exact ⟨rfl, rfl⟩
  · intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      by_cases same : session = freshWire
      · subst same; exact absurd (Or.inl rfl) outside
      · simp [LogicalProcessNetworkCore.Agrees, received, same]
    | session edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      by_cases same : session = freshWire
      · subst same; exact absurd (Or.inr (Or.inl rfl)) outside
      · simp [LogicalProcessNetworkCore.Agrees, received, same]
    | _ => rfl

def receiveStep : freshPlan.NetworkStep sent received where
  transition := .receive () freshWire escrowed [] 0 [] the_receive
  admissible := by intro _ held; cases held
  historyExact := rfl

theorem received_is_wellFormed : received.WellFormed :=
  ProcessPlan.wellFormed_preserved receiveStep
    (ProcessPlan.wellFormed_preserved sendStep
      (ProcessPlan.wellFormed_preserved spawnStep
        initial.initial_is_wellformed))

end
end Grass.Process.Tests.InitializedReceive
