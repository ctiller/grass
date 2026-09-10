import Grass.Process.Trace.Independence

/-! A receive acts on its receiver, so disjoint channel sessions alone cannot
justify commuting receives which use the same process instance slot. -/

namespace Grass.Process.Tests.ReceiveInterference

open Grass.Specification

universe u w v r m o

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o}
  {plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations}
  {a b c d : plan.LogicalProcessNetwork}
  {edge : plan.topology.ChannelKind}
  {first second : plan.topology.ChannelId edge}
  {firstOccurrence secondOccurrence : EdgeOccurrence plan.topology plan.message edge}
  {leftEmitted rightEmitted : Trace boundary.Observation}
  {leftIssued rightIssued : Bag (plan.topology.protocol (plan.topology.endpoints edge).2).Demand}
  {leftLocal rightLocal : ObservationSegment
    (plan.topology.protocol (plan.topology.endpoints edge).2).Observation}

/-- Even different sessions or generations touching the same receiver slot
cannot acquire the scope-disjointness premise needed for a commuting diamond. -/
theorem shared_receiver_not_independent
    (left : plan.Delivers a b edge first firstOccurrence leftEmitted leftIssued leftLocal)
    (right : plan.Delivers c d edge second secondOccurrence rightEmitted rightIssued rightLocal)
    (sameSlot : first.receiver.instanceId = second.receiver.instanceId) :
    ¬ (ProcessPlan.NetworkTransition.receive edge first firstOccurrence
        leftEmitted leftIssued leftLocal left).Independent
      (.receive edge second secondOccurrence rightEmitted rightIssued rightLocal right) := by
  intro independent
  apply independent (.instanceState (plan.topology.endpoints edge).2 first.receiver.instanceId)
  · simp [ProcessPlan.NetworkTransition.scope, ProcessPlan.DeliveryScope]
  · simp [ProcessPlan.NetworkTransition.scope, ProcessPlan.DeliveryScope, sameSlot]

/-- Distinct local observation choices remain distinct transition data even
when both choices have the same pre/post worlds and boundary output. -/
theorem different_local_outputs_remain_distinct
    (left : plan.Delivers a b edge first firstOccurrence leftEmitted leftIssued leftLocal)
    (right : plan.Delivers a b edge first firstOccurrence leftEmitted leftIssued rightLocal)
    (different : leftLocal ≠ rightLocal) :
    ProcessPlan.NetworkTransition.receive edge first firstOccurrence
        leftEmitted leftIssued leftLocal left ≠
      .receive edge first firstOccurrence leftEmitted leftIssued rightLocal right := by
  intro equal
  cases equal
  exact different rfl

end Grass.Process.Tests.ReceiveInterference
