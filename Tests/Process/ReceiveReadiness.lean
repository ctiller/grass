import Tests.Process.PreservationFixtures
import Tests.Process.EscrowReceiveUpdate

/-! Test-only readiness for the channel's escrow/cursor mechanism. The explicit
updated world realizes these guards as `EscrowDelivery`. An actual network
receive additionally requires the exact live receiver and its declared local
transition; the mechanism is deliberately no longer a `NetworkStep`.
`ChannelAgencyGap` checks that the formerly accepted absent-receiver frontier
cannot perform an actual receive. -/

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
def LedgerReady (before : ServerWorld) (session : serverTopology.ChannelId ())
    (occurrence : serverTopology.ChannelOccurrence () payload) : Prop :=
  session = wire ∧ occurrence = occurrenceOf ∧
    (before.inFlight () session).Outstanding escrowed ∧
    (before.sessions () session).delivered = 0

/-- The ledger operation for this exact session and occurrence. It supplies no
network-step witness or claim about receiver readiness. -/
structure LedgerReceive (before : ServerWorld)
    (session : serverTopology.ChannelId ())
    (occurrence : serverTopology.ChannelOccurrence () payload) : Type 1 where
  after : ServerWorld
  delivery : serverPlan.EscrowDelivery before after () session escrowed
  occurrenceExact : occurrence = occurrenceOf

/-- Every tagged ledger receive exposes the channel relation's pre-state guards. -/
theorem ledger_receive_implies_ready {before : ServerWorld}
    {session : serverTopology.ChannelId ()}
    {occurrence : serverTopology.ChannelOccurrence () payload}
    (actual : LedgerReceive before session occurrence) : LedgerReady before session occurrence := by
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

noncomputable def readyLedgerReceive {before : ServerWorld}
    {session : serverTopology.ChannelId ()}
    {occurrence : serverTopology.ChannelOccurrence () payload}
    (ready : LedgerReady before session occurrence) : LedgerReceive before session occurrence := by
  rcases ready with ⟨rfl, rfl, outstanding, atZero⟩
  let after := receiveAfter before outstanding
  have delivery : serverPlan.EscrowDelivery before after () wire escrowed := by
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
      occurrenceExact := rfl }

/-- For this fixture's channel relation, the concrete ledger/cursor guards are
exactly enough to construct the escrow/cursor operation at any world. This
says nothing about a live receiver or subsequent local process handling. -/
theorem ready_iff_ledger_receive {before : ServerWorld}
    {session : serverTopology.ChannelId ()}
    {occurrence : serverTopology.ChannelOccurrence () payload} :
    LedgerReady before session occurrence ↔ Nonempty (LedgerReceive before session occurrence) := by
  constructor
  · exact fun ready => ⟨readyLedgerReceive ready⟩
  · rintro ⟨actual⟩
    exact ledger_receive_implies_ready actual

/-- The existing send-produced frontier satisfies the concrete guards. -/
theorem sent_is_ready : LedgerReady sent wire occurrenceOf := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact the_receive_after_the_send.wasOutstanding
  · exact the_receive_after_the_send.contractual.2.2.1

/-- An enabled receive at the concrete send-produced frontier. Its resolution,
cursor and frame obligations come from the existing `Delivers` witness;
this does not construct a receive from the readiness guards. -/
noncomputable def sent_ledger_receive : LedgerReceive sent wire occurrenceOf where
  after := received
  delivery := the_receive_after_the_send
  occurrenceExact := rfl

/-- Once resolved, the same occurrence is no longer receive-ready. -/
theorem resolved_is_not_ready : ¬ LedgerReady received wire occurrenceOf := by
  rintro ⟨_, _, outstanding, _⟩
  rw [received_wire] at outstanding
  rcases outstanding with ⟨_, unresolved⟩
  rw [settled_resolution] at unresolved
  contradiction

/-- Before the send, the missing occurrence is not receive-ready. -/
theorem missing_is_not_ready : ¬ LedgerReady withRoot wire occurrenceOf := by
  rintro ⟨_, _, outstanding, _⟩
  change (EscrowLedger.empty).Outstanding escrowed at outstanding
  exact List.not_mem_nil outstanding.1

theorem resolved_has_no_ledger_receive :
    ¬ Nonempty (LedgerReceive received wire occurrenceOf) := by
  rintro ⟨actual⟩
  exact resolved_is_not_ready (ledger_receive_implies_ready actual)

theorem missing_has_no_ledger_receive :
    ¬ Nonempty (LedgerReceive withRoot wire occurrenceOf) := by
  rintro ⟨actual⟩
  exact missing_is_not_ready (ledger_receive_implies_ready actual)

/-- Naming the concrete later-epoch session cannot satisfy readiness. -/
theorem sidewire_is_not_ready : ¬ LedgerReady sent sidewire occurrenceOf := by
  intro ready
  exact sidewire_ne_wire ready.1

theorem wrong_session_is_not_ready {session : serverTopology.ChannelId ()}
    (wrong : session ≠ wire) : ¬ LedgerReady sent session occurrenceOf := by
  intro ready
  exact wrong ready.1

/-- The same session mismatch rules out the corresponding receive relation,
independently of other transition constructors. -/
theorem wrong_session_has_no_delivery {before after : ServerWorld}
    {session : serverTopology.ChannelId ()} (wrong : session ≠ wire) :
    ¬ serverPlan.EscrowDelivery before after () session escrowed := by
  intro delivery
  have onWire : escrowed.2.1 = wire := delivery.contractual.1
  have onSession : escrowed.2.1 = session := delivery.onItsSession
  exact wrong (onSession.symm.trans onWire)

theorem wrong_session_has_no_ledger_receive {before : ServerWorld}
    {session : serverTopology.ChannelId ()} (wrong : session ≠ wire) :
    ¬ Nonempty (LedgerReceive before session occurrenceOf) := by
  rintro ⟨actual⟩
  exact wrong (ledger_receive_implies_ready actual).1

/-- The later epoch is an inhabited negative control for the ledger operation. -/
theorem sidewire_has_no_ledger_receive :
    ¬ Nonempty (LedgerReceive sent sidewire occurrenceOf) :=
  wrong_session_has_no_ledger_receive sidewire_ne_wire

end

end Grass.Process.Tests.ReceiveReadiness
