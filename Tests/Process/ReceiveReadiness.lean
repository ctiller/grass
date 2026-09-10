import Tests.Process.PreservationFixtures
import Tests.Process.EscrowReceiveUpdate

/-! A test-only receive-readiness experiment.  Readiness is stated from the
channel's concrete operational guards, then connected to a receive-tagged
`NetworkStep`; it is not defined as existence of that step.  The equivalence
below proves neither that a receiver is live nor that a local process handles
the delivered value.  `Tests/Process/ChannelAgencyGap.lean`'s initialized world
with no receiver is the concrete counterexample separating those claims. -/

namespace Grass.Process.Tests.ReceiveReadiness

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (serverMessage ServerWorld withRoot)
open Grass.Process.Tests.Channel (wire)
open Grass.Process.Tests.Transition
open Grass.Process.Tests.Reroute (sidewire sidewire_ne_wire)
open Grass.Process.Tests.EscrowReceiveUpdate

noncomputable section

open Classical

/-- The pre-state guards selected by this concrete channel contract, retaining
the exact session and occurrence. -/
def Ready (before : ServerWorld) (session : serverTopology.ChannelId ())
    (occurrence : serverTopology.ChannelOccurrence () payload) : Prop :=
  session = wire ∧ occurrence = occurrenceOf ∧
    (before.inFlight () session).Outstanding escrowed ∧
    (before.sessions () session).delivered = 0

/-- A network step whose constructor is specifically the receive of this exact
session and occurrence. Other enabled transition constructors are irrelevant. -/
structure ActualReceive (before : ServerWorld)
    (session : serverTopology.ChannelId ())
    (occurrence : serverTopology.ChannelOccurrence () payload) : Type 1 where
  after : ServerWorld
  delivery : serverPlan.Delivers before after () session escrowed
  step : serverPlan.NetworkStep before after
  tagged : step.transition = .receive () session escrowed delivery
  occurrenceExact : occurrence = occurrenceOf

/-- Every tagged actual receive exposes the channel relation's pre-state guards. -/
theorem actual_receive_implies_ready {before : ServerWorld}
    {session : serverTopology.ChannelId ()}
    {occurrence : serverTopology.ChannelOccurrence () payload}
    (actual : ActualReceive before session occurrence) : Ready before session occurrence := by
  have onWire : escrowed.2.1 = wire := actual.delivery.contractual.1
  have onSession : escrowed.2.1 = session := actual.delivery.onItsSession
  have sameSession : session = wire := onSession.symm.trans onWire
  subst session
  refine ⟨rfl, actual.occurrenceExact, ?_, ?_⟩
  · exact actual.delivery.wasOutstanding
  · have atZero := actual.delivery.contractual.2.2.1
    exact atZero

noncomputable def receiveAfter (before : ServerWorld)
    (outstanding : (before.inFlight () wire).Outstanding escrowed) : ServerWorld :=
  { before with
      inFlight := fun _ session =>
        if session = wire then receiveUpdate (before.inFlight () wire) escrowed outstanding
        else before.inFlight () session
      sessions := fun _ session =>
        if session = wire then
          { before.sessions () wire with
              delivered := (before.sessions () wire).delivered + 1 }
        else before.sessions () session }

@[simp] theorem receiveAfter_wire_inFlight (before : ServerWorld)
    (outstanding : (before.inFlight () wire).Outstanding escrowed) :
    (receiveAfter before outstanding).inFlight () wire =
      receiveUpdate (before.inFlight () wire) escrowed outstanding := by
  simp [receiveAfter]

@[simp] theorem receiveAfter_wire_session (before : ServerWorld)
    (outstanding : (before.inFlight () wire).Outstanding escrowed) :
    (receiveAfter before outstanding).sessions () wire =
      { before.sessions () wire with
          delivered := (before.sessions () wire).delivered + 1 } := by
  simp [receiveAfter]

noncomputable def readyActualReceive {before : ServerWorld}
    {session : serverTopology.ChannelId ()}
    {occurrence : serverTopology.ChannelOccurrence () payload}
    (ready : Ready before session occurrence) : ActualReceive before session occurrence := by
  rcases ready with ⟨rfl, rfl, outstanding, atZero⟩
  let after := receiveAfter before outstanding
  have delivery : serverPlan.Delivers before after () wire escrowed := by
    refine
      { contractual := ⟨rfl, outstanding, atZero, ?_⟩
        onItsSession := rfl
        wasOutstanding := outstanding
        nowResolved := ?_
        ledgerExtends := ?_
        resolvesNothingElse := ?_
        createsNothing := ?_
        requestsNothing := ?_
        cursorAdvances := ?_
        statusUnchanged := ?_
        scope := ?_ }
    · simp [after, receiveAfter]
    · rw [show after.inFlight () wire =
          receiveUpdate (before.inFlight () wire) escrowed outstanding by
            simp [after]]
      exact receiveUpdate_resolution_self (before.inFlight () wire) escrowed outstanding
    · rw [show after.inFlight () wire =
          receiveUpdate (before.inFlight () wire) escrowed outstanding by
            simp [after]]
      exact receiveUpdate_extends (before.inFlight () wire) escrowed outstanding
    · rw [show after.inFlight () wire =
          receiveUpdate (before.inFlight () wire) escrowed outstanding by
            simp [after]]
      exact receiveUpdate_resolves_nothing_else (before.inFlight () wire) escrowed outstanding
    · rw [show after.inFlight () wire =
          receiveUpdate (before.inFlight () wire) escrowed outstanding by
            simp [after]]
      exact receiveUpdate_creates_nothing (before.inFlight () wire) escrowed outstanding
    · rw [show after.inFlight () wire =
          receiveUpdate (before.inFlight () wire) escrowed outstanding by
            simp [after]]
      exact receiveUpdate_requests_nothing (before.inFlight () wire) escrowed outstanding
    · simp [after]
    · simp [after]
    · intro fragment outside
      cases fragment with
      | escrow edge other =>
          have edgeIsUnit : edge = () := rfl
          subst edgeIsUnit
          change serverTopology.ChannelId () at other
          have different : other ≠ wire := by
            intro same
            subst same
            exact outside (Or.inl rfl)
          change before.inFlight () other = after.inFlight () other
          rw [show after.inFlight () other = before.inFlight () other by
            dsimp [after, receiveAfter]
            rw [if_neg different]]
      | session edge other =>
          have edgeIsUnit : edge = () := rfl
          subst edgeIsUnit
          change serverTopology.ChannelId () at other
          have different : other ≠ wire := by
            intro same
            subst same
            exact outside (Or.inr rfl)
          change before.sessions () other = after.sessions () other
          rw [show after.sessions () other = before.sessions () other by
            dsimp [after, receiveAfter]
            rw [if_neg different]]
      | _ => rfl
  refine
    { after := after
      delivery := delivery
      step :=
        { transition := .receive () wire escrowed delivery
          admissible := by intro _ absent; cases absent
          historyExact := rfl }
      tagged := rfl
      occurrenceExact := rfl }

/-- For this fixture's channel relation, the concrete ledger/cursor guards are
exactly enough to construct a receive-tagged network step at any world.  This
says nothing about a live receiver or subsequent local process handling. -/
theorem ready_iff_actual_receive {before : ServerWorld}
    {session : serverTopology.ChannelId ()}
    {occurrence : serverTopology.ChannelOccurrence () payload} :
    Ready before session occurrence ↔ Nonempty (ActualReceive before session occurrence) := by
  constructor
  · exact fun ready => ⟨readyActualReceive ready⟩
  · rintro ⟨actual⟩
    exact actual_receive_implies_ready actual

/-- The existing send-produced frontier satisfies the concrete guards. -/
theorem sent_is_ready : Ready sent wire occurrenceOf := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact the_receive_after_the_send.wasOutstanding
  · exact the_receive_after_the_send.contractual.2.2.1

/-- An enabled receive at the concrete send-produced frontier. Its resolution,
cursor and frame obligations come from the existing `Delivers` witness;
this does not construct a receive from the readiness guards. -/
noncomputable def sent_actual_receive : ActualReceive sent wire occurrenceOf where
  after := received
  delivery := the_receive_after_the_send
  step := Grass.Process.Tests.Preservation.theReceiveStep
  tagged := rfl
  occurrenceExact := rfl

/-- Once resolved, the same occurrence is no longer receive-ready. -/
theorem resolved_is_not_ready : ¬ Ready received wire occurrenceOf := by
  rintro ⟨_, _, outstanding, _⟩
  rw [received_wire] at outstanding
  rcases outstanding with ⟨_, unresolved⟩
  rw [settled_resolution] at unresolved
  contradiction

/-- Before the send, the missing occurrence is not receive-ready. -/
theorem missing_is_not_ready : ¬ Ready withRoot wire occurrenceOf := by
  rintro ⟨_, _, outstanding, _⟩
  change (EscrowLedger.empty).Outstanding escrowed at outstanding
  exact List.not_mem_nil outstanding.1

theorem resolved_has_no_actual_receive :
    ¬ Nonempty (ActualReceive received wire occurrenceOf) := by
  rintro ⟨actual⟩
  exact resolved_is_not_ready (actual_receive_implies_ready actual)

theorem missing_has_no_actual_receive :
    ¬ Nonempty (ActualReceive withRoot wire occurrenceOf) := by
  rintro ⟨actual⟩
  exact missing_is_not_ready (actual_receive_implies_ready actual)

/-- Naming the concrete later-epoch session cannot satisfy readiness. -/
theorem sidewire_is_not_ready : ¬ Ready sent sidewire occurrenceOf := by
  intro ready
  exact sidewire_ne_wire ready.1

theorem wrong_session_is_not_ready {session : serverTopology.ChannelId ()}
    (wrong : session ≠ wire) : ¬ Ready sent session occurrenceOf := by
  intro ready
  exact wrong ready.1

/-- The same session mismatch rules out the corresponding receive relation,
independently of other transition constructors. -/
theorem wrong_session_has_no_delivery {before after : ServerWorld}
    {session : serverTopology.ChannelId ()} (wrong : session ≠ wire) :
    ¬ serverPlan.Delivers before after () session escrowed := by
  intro delivery
  have onWire : escrowed.2.1 = wire := delivery.contractual.1
  have onSession : escrowed.2.1 = session := delivery.onItsSession
  exact wrong (onSession.symm.trans onWire)

theorem wrong_session_has_no_actual_receive {before : ServerWorld}
    {session : serverTopology.ChannelId ()} (wrong : session ≠ wire) :
    ¬ Nonempty (ActualReceive before session occurrenceOf) := by
  rintro ⟨actual⟩
  exact wrong (actual_receive_implies_ready actual).1

/-- The later epoch is an inhabited negative control for the tagged step. -/
theorem sidewire_has_no_actual_receive :
    ¬ Nonempty (ActualReceive sent sidewire occurrenceOf) :=
  wrong_session_has_no_actual_receive sidewire_ne_wire

end

end Grass.Process.Tests.ReceiveReadiness
