import Tests.Process.ProcessStepFixtures
import Tests.Process.PreservationFixtures
import Grass.Process.Network.Receive

/-!
# Channel receiver agency regression

The former initialized absent-receiver example still permits asynchronous send,
but can no longer receive. Every actual receive performs the receiver's declared
local event; unrelated instances remain framed. This is receiver agency only,
not deadlock freedom or general local-event provenance. The separate local
result witness below is not asserted reachable from an exact initial network.
An external result need not come from a channel; this example does not call
the tick invalid. It shows that the local step alone supplies no channel source
evidence, which an internally routed result would additionally need.
-/

namespace Grass.Process.Tests.ChannelAgencyGap

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Channel (wire)
open Grass.Process.Tests.Transition (serverPlan escrowed)
open Grass.Process.Tests.ProcessStep (busy busyAfter the_listener_ticks)
open Grass.Process.Tests.Transition (sent)
open Grass.Process.Tests.Preservation
  (withRoot_is_a_start theSendStep)

variable {emitted : Trace fixtureBoundary.Observation}
  {issued : Bag Demand} {localEmitted : ObservationSegment Observation}

/-- Sending does not require an already-ready receiver. This exact initialized
send remains legal and leaves the message in escrow. -/
theorem initialized_send :
    Nonempty (serverPlan.ExactInitialNetwork ⟨0⟩ World.withRoot) ∧
    Nonempty (serverPlan.NetworkStep World.withRoot sent) :=
  ⟨⟨withRoot_is_a_start⟩, ⟨theSendStep⟩⟩

/-- The exact receiving incarnation named by the session has no instance at
the reached frontier. -/
theorem receive_frontier_has_no_receiver :
    sent.instances (serverTopology.endpoints ()).2 wire.receiver.instanceId = none := rfl

/-- A missing receiver excludes consumption even with valid outstanding escrow. -/
theorem missing_receiver_cannot_receive
    {before after : serverPlan.LogicalProcessNetwork}
    {edge : serverTopology.ChannelKind} {session : serverTopology.ChannelId edge}
    {occurrence : EdgeOccurrence serverTopology serverPlan.message edge}
    (missing : before.instances (serverTopology.endpoints edge).2
      session.receiver.instanceId = none) :
    ¬ serverPlan.Delivers before after edge session occurrence emitted issued localEmitted :=
  ProcessPlan.Delivers.impossible_without_receiver missing

/-- The previously accepted initialized receive is now rejected. -/
theorem initialized_absent_receiver_cannot_receive
    {after : serverPlan.LogicalProcessNetwork} :
    ¬ serverPlan.Delivers sent after () wire escrowed emitted issued localEmitted :=
  missing_receiver_cannot_receive receive_frontier_has_no_receiver

/-- Replace only the receiving slot for the two rejection controls below. -/
noncomputable def receiverWorld (receiver : ProcessInstance serverTopology) : ServerWorld :=
  { Transition.beforeReceive with
      instances := fun kind slot =>
        match kind with
        | .listener => Transition.beforeReceive.instances .listener slot
        | .connection => if slot = wire.receiver.instanceId then some receiver
            else Transition.beforeReceive.instances .connection slot }

@[simp] theorem receiverWorld_slot (receiver : ProcessInstance serverTopology) :
    (receiverWorld receiver).instances .connection wire.receiver.instanceId = some receiver := by
  simp [receiverWorld]

def staleReceiver : ProcessInstance serverTopology :=
  { Instances.counting with ref := connectionSeven 1 }

/-- The right numeric slot with the wrong incarnation cannot consume an old
session's message, even though that replacement instance is live. -/
theorem stale_generation_cannot_receive {after : ServerWorld} :
    ¬ serverPlan.Delivers (receiverWorld staleReceiver) after () wire escrowed emitted issued localEmitted := by
  intro delivery
  obtain ⟨sameKind, sameRef⟩ := delivery.receiverRef staleReceiver
    (receiverWorld_slot staleReceiver)
  have impossible : (1 : Nat) = 0 := by
    exact congrArg (fun reference => reference.generation.carrier) sameRef
  contradiction

def stoppedReceiver : ProcessInstance serverTopology :=
  { Instances.counting with localState := ⟨0⟩ }

/-- Receiver identity and escrow availability are insufficient when the
receiver's actual protocol does not admit the arrival. -/
theorem unhandled_arrival_cannot_receive {after : ServerWorld} :
    ¬ serverPlan.Delivers (receiverWorld stoppedReceiver) after () wire escrowed emitted issued localEmitted := by
  intro delivery
  let effects := delivery.receiverStep
  obtain ⟨fromInstance, toInstance, fromKind, toKind, foundFrom, _, localStep, _⟩ :=
    effects.protocolStep
  change some stoppedReceiver = some fromInstance at foundFrom
  cases foundFrom
  exact localStep.1 rfl

/-- An actual local result step, wrapped with the freshness and history laws
that distinguish a `NetworkStep` from a bare transition witness. -/
def localResultStep : serverPlan.NetworkStep (busy 2) (busyAfter 2) where
  transition := .processStep .listener () (.result .tick ()) [Observation.beep] 0
    [Observation.beep] (the_listener_ticks 2 (by decide) ())
  admissible := by
    intro nominal allocated
    have empty : nominal ∈ (Allocation.empty : Allocation serverTopology.Carrier).entries :=
      allocated
    exact absurd empty List.not_mem_nil
  historyExact := rfl

/-- The local result witness begins with no escrowed message on any server edge
or session. -/
theorem local_result_starts_with_empty_escrow
    (session : serverTopology.ChannelId ()) :
    (busy 2).inFlight () session = EscrowLedger.empty := rfl

/-- In particular, the exact channel occurrence used by the server fixture is
not outstanding before the local result step. -/
theorem local_result_has_no_channel_receipt :
    ¬ ((busy 2).inFlight () wire).Outstanding escrowed := by
  change ¬ (EscrowLedger.empty).Outstanding escrowed
  intro outstanding
  exact List.not_mem_nil outstanding.1

/-- No receive transition for that occurrence can start at the local-result
frontier, because `Delivers.wasOutstanding` would contradict the empty ledger. -/
theorem local_result_has_no_delivery {after : serverPlan.LogicalProcessNetwork} :
    ¬ serverPlan.Delivers (busy 2) after () wire escrowed emitted issued localEmitted := by
  intro delivery
  have outstanding := delivery.wasOutstanding
  change (EscrowLedger.empty).Outstanding escrowed at outstanding
  exact local_result_has_no_channel_receipt outstanding

/-- The empty frontier excludes every channel receive, not only the occurrence
chosen by the older fixture. This says nothing about genuine external results. -/
theorem local_result_has_no_delivery_on_any_session
    {after : serverPlan.LogicalProcessNetwork}
    {edge : serverTopology.ChannelKind} {session : serverTopology.ChannelId edge}
    {occurrence : EdgeOccurrence serverTopology serverPlan.message edge} :
    ¬ serverPlan.Delivers (busy 2) after edge session occurrence emitted issued localEmitted := by
  intro delivery
  cases edge
  have outstanding := delivery.wasOutstanding
  change EscrowLedger.empty.Outstanding occurrence at outstanding
  exact List.not_mem_nil outstanding.1

/-- Every other instance slot remains framed across an actual receive. -/
theorem receive_preserves_unrelated_instance
    {before after : serverPlan.LogicalProcessNetwork}
    {edge : serverTopology.ChannelKind} {session : serverTopology.ChannelId edge}
    {occurrence : EdgeOccurrence serverTopology serverPlan.message edge}
    (delivery : serverPlan.Delivers before after edge session occurrence emitted issued localEmitted)
    (kind : serverTopology.ProcessKind) (slot : serverTopology.InstanceId kind)
    (unrelated : NetworkFragment.instanceState kind slot ≠
      NetworkFragment.instanceState (serverTopology.endpoints edge).2 session.receiver.instanceId) :
    before.instances kind slot = after.instances kind slot :=
  delivery.frames_other_instance kind slot unrelated

/-- Arrival retains all old receiver demands, adding only those issued by its
actual local transition. It does not manufacture a dependent result. -/
theorem arrival_settlement_adds_only_issued
    {edge : serverTopology.ChannelKind}
    {occurrence : EdgeOccurrence serverTopology serverPlan.message edge}
    (issued old next : Bag (serverTopology.protocol (serverTopology.endpoints edge).2).Demand)
    (settles : serverPlan.SettlesDemands
      ((serverPlan.channel edge).receiverInput.arrives occurrence.1) issued old next) :
    next = old + issued := by
  unfold ProcessPlan.SettlesDemands at settles
  rw [(serverPlan.channel edge).receiverInput.arrivesUnsettled occurrence.1] at settles
  exact settles

end Grass.Process.Tests.ChannelAgencyGap
