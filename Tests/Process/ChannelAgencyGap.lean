import Tests.Process.ProcessStepFixtures
import Tests.Process.PreservationFixtures

/-!
# Channel agency gap diagnostic

This fixture records two present interface facts. A local result step can be
an actual network step while every channel ledger is empty, and a receive
preserves every process-instance fragment.  It does not claim that no future
plan can express blocking, nor that the local result witness below is reachable
from an exact initial network.
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
open Grass.Process.Tests.Transition (sent received)
open Grass.Process.Tests.Preservation
  (withRoot_is_a_start theSendStep theReceiveStep)

/-- This example starts at an exact initial network, then sends and receives
through the existing canonical fixture steps. -/
theorem initialized_send_receive :
    Nonempty (serverPlan.ExactInitialNetwork ⟨0⟩ World.withRoot) ∧
    Nonempty (serverPlan.NetworkStep World.withRoot sent) ∧
    Nonempty (serverPlan.NetworkStep sent received) :=
  ⟨⟨withRoot_is_a_start⟩, ⟨theSendStep⟩, ⟨theReceiveStep⟩⟩

/-- The exact receiving incarnation named by the session has no instance at
the reached delivery frontier. The current receive step still exists. -/
theorem receive_frontier_has_no_receiver :
    sent.instances (serverTopology.endpoints ()).2 wire.receiver.instanceId = none := rfl

/-- Delivery does not install or run a receiver either. -/
theorem receive_leaves_no_receiver :
    received.instances (serverTopology.endpoints ()).2 wire.receiver.instanceId = none := rfl

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
    ¬ serverPlan.Delivers (busy 2) after () wire escrowed := by
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
    ¬ serverPlan.Delivers (busy 2) after edge session occurrence := by
  intro delivery
  cases edge
  have outstanding := delivery.wasOutstanding
  change EscrowLedger.empty.Outstanding occurrence at outstanding
  exact List.not_mem_nil outstanding.1

/-- A receive transition preserves every instance slot: its declared scope is
only the exact session's escrow and cursor. -/
theorem receive_preserves_instance
    {before after : serverPlan.LogicalProcessNetwork}
    {edge : serverTopology.ChannelKind} {session : serverTopology.ChannelId edge}
    {occurrence : EdgeOccurrence serverTopology serverPlan.message edge}
    (delivery : serverPlan.Delivers before after edge session occurrence)
    (kind : serverTopology.ProcessKind) (slot : serverTopology.InstanceId kind) :
    before.instances kind slot = after.instances kind slot := by
  exact delivery.scope (.instanceState kind slot) (by simp)

/-- Hence a receive cannot itself consume or alter the outstanding bag stored
in a receiver instance; any such local transition is separate from `Delivers`. -/
theorem receive_preserves_receiver_outstanding
    {before after : serverPlan.LogicalProcessNetwork}
    {edge : serverTopology.ChannelKind} {session : serverTopology.ChannelId edge}
    {occurrence : EdgeOccurrence serverTopology serverPlan.message edge}
    (delivery : serverPlan.Delivers before after edge session occurrence)
    (slot : serverTopology.InstanceId (serverTopology.endpoints edge).2)
    (incarnation : ProcessInstance serverTopology)
    (found : before.instances (serverTopology.endpoints edge).2 slot = some incarnation) :
    ∃ same, after.instances (serverTopology.endpoints edge).2 slot = some same ∧
      same.outstanding = incarnation.outstanding := by
  have sameSlot := receive_preserves_instance delivery (serverTopology.endpoints edge).2 slot
  rw [found] at sameSlot
  exact ⟨incarnation, sameSlot.symm, rfl⟩

end Grass.Process.Tests.ChannelAgencyGap
