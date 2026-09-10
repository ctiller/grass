import Grass.Process.Network.Transition

/-! Test-only exhaustive transition analysis for the channel deadlock experiment.
This identifies actual delivery, not process progress or demand settlement. -/

namespace Grass.Process.Tests.ReceiveCoverage

open Grass.Specification

universe u w v r m o

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o}
  {plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations}
  {before after : plan.LogicalProcessNetwork}

private theorem cursor_frame {edge : plan.topology.ChannelKind}
    {session : plan.topology.ChannelId edge}
    (agrees : LogicalProcessNetworkCore.Agrees (.session edge session) before after) :
    (before.sessions edge session).delivered = (after.sessions edge session).delivered :=
  congrArg ChannelSession.delivered agrees

private theorem scoped_cursor_unchanged
    {edge : plan.topology.ChannelKind} {session : plan.topology.ChannelId edge}
    (scope : plan.TouchesOnly before after
      (fun fragment => fragment = .escrow edge session ∨ fragment = .session edge session))
    (same : (after.sessions edge session).delivered = (before.sessions edge session).delivered)
    (target : plan.topology.ChannelKind) (key : plan.topology.ChannelId target) :
    (before.sessions target key).delivered = (after.sessions target key).delivered := by
  classical
  by_cases hit : NetworkFragment.session target key = NetworkFragment.session edge session
  · cases hit
    exact same.symm
  · exact cursor_frame (scope (.session target key) (by simp [hit]))

/-- Every transition which changes a delivery cursor is an actual receive on
that exact session, retaining the constructor and its delivery witness.
All other constructors, including cancellation, close, death and reroute, are
checked against their actual frame/cursor laws. This does not say that those
other transitions cannot discharge a process obligation in some other way. -/
theorem cursor_change_has_delivery
    (transition : plan.NetworkTransition before after)
    (target : plan.topology.ChannelKind) (key : plan.topology.ChannelId target)
    (changed : (before.sessions target key).delivered ≠
      (after.sessions target key).delivered) :
    ∃ (occurrence : EdgeOccurrence plan.topology plan.message target)
      (emitted : Trace boundary.Observation)
      (issued : Bag (plan.topology.protocol (plan.topology.endpoints target).2).Demand)
      (localEmitted : ObservationSegment
        (plan.topology.protocol (plan.topology.endpoints target).2).Observation)
      (delivery : plan.Delivers before after target key occurrence emitted issued localEmitted),
      transition = .receive target key occurrence emitted issued localEmitted delivery := by
  classical
  cases transition with
  | receive edge session occurrence emitted issued localEmitted delivery =>
    by_cases hit : NetworkFragment.session target key = NetworkFragment.session edge session
    · cases hit
      exact ⟨occurrence, emitted, issued, localEmitted, delivery, rfl⟩
    · exact False.elim (changed (cursor_frame
        (delivery.scope (.session target key) (by simp [ProcessPlan.DeliveryScope, hit]))))
  | channelClose _ _ _ step =>
    exact False.elim (changed (scoped_cursor_unchanged step.scope step.cursorUnchanged target key))
  | channelDeath _ _ _ step =>
    exact False.elim (changed (scoped_cursor_unchanged step.scope step.cursorUnchanged target key))
  | processStep _ _ _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | spawn _ _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | restart _ _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | send _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | commit _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | requestCancel _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | acknowledgeCancel _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | timeout _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | senderDeath _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | receiverDeath _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | drop _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | reroute _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | coalesce _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | interrupt _ _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | fault _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | environmentViolation _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | childCancelled _ _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | childDied _ _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | processTermination _ _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | join _ _ _ step =>
    exact False.elim (changed (cursor_frame (step.scope (.session target key) (by simp))))
  | detach _ _ step =>
    exact False.elim (changed (cursor_frame (step.onlyThatSlot.scope (.session target key) (by simp))))

end Grass.Process.Tests.ReceiveCoverage
