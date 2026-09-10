import Grass.Process.Network.Transition

/-! Receiver facts derived from the actual atomic channel consume. These laws
do not classify other local-event sources or establish network deadlock freedom. -/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o}
  {plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations}
  {before after : plan.LogicalProcessNetwork}
  {edge : plan.topology.ChannelKind} {session : plan.topology.ChannelId edge}
  {occurrence : EdgeOccurrence plan.topology plan.message edge}
  {emitted : Trace boundary.Observation}
  {issued : Bag (plan.topology.protocol (plan.topology.endpoints edge).2).Demand}
  {localEmitted : ObservationSegment
    (plan.topology.protocol (plan.topology.endpoints edge).2).Observation}

namespace ProcessPlan.Delivers

/-- Consumption names the live receiver incarnation already present in the
reached pre-world, including the generation carried by this exact session. -/
theorem receiver_is_live (delivery : plan.Delivers before after edge session occurrence emitted issued localEmitted) :
    ∃ incarnation,
      before.instances (plan.topology.endpoints edge).2 session.receiver.instanceId =
        some incarnation ∧
      incarnation.Live ∧
      ∃ sameKind : incarnation.kind = (plan.topology.endpoints edge).2,
        sameKind ▸ incarnation.ref = session.receiver := by
  let effects := delivery.receiverStep
  obtain ⟨incarnation, found, live, _⟩ := effects.from'
  exact ⟨incarnation, found, live, delivery.receiverRef incarnation found⟩

/-- An outstanding message alone cannot be consumed by an absent receiver. -/
theorem impossible_without_receiver
    (missing : before.instances (plan.topology.endpoints edge).2
      session.receiver.instanceId = none) :
    ¬ plan.Delivers before after edge session occurrence emitted issued localEmitted := by
  intro delivery
  obtain ⟨_, found, _⟩ := delivery.receiver_is_live
  rw [missing] at found
  cases found

/-- All other instance slots retain their complete state and outstanding bag. -/
theorem frames_other_instance
    (delivery : plan.Delivers before after edge session occurrence emitted issued localEmitted)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
    (unrelated : NetworkFragment.instanceState kind slot ≠
      NetworkFragment.instanceState (plan.topology.endpoints edge).2 session.receiver.instanceId) :
    before.instances kind slot = after.instances kind slot := by
  exact delivery.scope (.instanceState kind slot)
    (by simp [ProcessPlan.DeliveryScope, unrelated])

/-- The receiver's actual protocol transition keeps every old demand and adds
only its declared issued bag: a channel arrival itself is not a demand answer. -/
theorem receiver_demand_equation
    (delivery : plan.Delivers before after edge session occurrence emitted issued localEmitted) :
    ∃ (fromInstance toInstance : ProcessInstance plan.topology)
      (fromKind : fromInstance.kind = (plan.topology.endpoints edge).2)
      (toKind : toInstance.kind = (plan.topology.endpoints edge).2),
      before.instances (plan.topology.endpoints edge).2 session.receiver.instanceId =
        some fromInstance ∧
      after.instances (plan.topology.endpoints edge).2 session.receiver.instanceId =
        some toInstance ∧
      (plan.topology.protocol (plan.topology.endpoints edge).2).Step
        (fromKind ▸ fromInstance.localState)
        ((plan.channel edge).receiverInput.arrives occurrence.1)
        (toKind ▸ toInstance.localState) issued localEmitted ∧
      (toKind ▸ toInstance.outstanding) = (fromKind ▸ fromInstance.outstanding) + issued := by
  let effects := delivery.receiverStep
  obtain ⟨fromInstance, toInstance, fromKind, toKind, foundFrom, foundTo,
    protocolStep, settles, _⟩ := effects.protocolStep
  refine ⟨fromInstance, toInstance, fromKind, toKind,
    foundFrom, foundTo, protocolStep, ?_⟩
  simpa [ProcessPlan.SettlesDemands,
    (plan.channel edge).receiverInput.arrivesUnsettled occurrence.1] using settles

end ProcessPlan.Delivers
end Grass.Process
