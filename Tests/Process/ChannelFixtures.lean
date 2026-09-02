import Grass.Process.Network.Channel
import Tests.Process.WorldFixtures

/-!
# A channel contract that sends and receives, and one that cannot exist

`Grass/Process/Network/Channel.lean` replaces three of `docs/PROCESS.md` §3's
opaque law fields with a footprint discipline and derives the laws. That trade
is worth making only if the discipline is satisfiable by a contract that
actually does something, and restrictive enough to reject one that does not.

An earlier revision of this file failed the first half. Its contract had
`Receive := fun _ _ _ _ => False`, a `Send` that forced `before = after`, and
`pure True` for `SendPre`, `SenderPost` and `ReceiverPost` — so every triple was
vacuous, no fixture invoked `send` or `receive`, and the header claimed the
discipline was shown "satisfiable by a real contract" on that evidence.

`liveChannel` below sends and receives. Its receive takes `quiet` to
`afterDelivery`, consumes `ReceiverPre * Escrow`, and establishes a
`ReceiverPost` that is false before the step and true after — so
`receive_advances_the_cursor` is a fact about a state change and not about an
empty relation.

The negative halves:

* `escrow_reading_a_region_is_impossible` — an escrow assertion that reads a
  shared region cannot be any contract's `Escrow`. An opaque
  `escrowStable : StableUnderUnrelatedProcessSteps Escrow` field could not have
  rejected it, because nothing would check the supplied value was one.
* `sends_cannot_happen_on_a_closed_session` — the vacuity route an earlier
  revision of the *module* left open. With the session law as a hypothesis of
  `send` alone, a contract could set `SessionOpen` to a never-satisfiable
  assertion and discharge `send` for free while sends genuinely occurred.
  `sendOnOpenSession` closes it, and this is that closed.
-/

namespace Grass.Process.Tests.Channel

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld serverAgreement quiet afterAccept)

/-- The message type on the one edge. -/
abbrev ServerMessage := World.serverMessage ()

/-- The one session this fixture sends on. -/
def wire : serverTopology.ChannelId () where
  sender := Instances.listenerZero
  receiver := connectionSeven 0
  epoch := ⟨.channelEpoch, 0⟩
  isEpoch := rfl

/--
The world after the receiver has consumed one occurrence.

Uniform over sessions rather than keyed on `wire`, because `ChannelId` has no
decidable equality and this fixture has one session anyway.
-/
def afterDelivery : ServerWorld :=
  { quiet with sessions := fun _ _ => ⟨.open, 1⟩ }

/-- A send discharges the listener's `log` demand. -/
def serverSenderOutput :
    SenderDemandEmbedding serverTopology .listener ServerMessage where
  emits := fun _ => .log

/-- And arrives at the connection as external entropy, settling nothing. -/
def serverReceiverInput :
    ReceiverEventEmbedding serverTopology .connection ServerMessage where
  arrives := fun _ => .external .wake
  arrivesUnsettled := fun _ => rfl

/--
The step relations.

`Receive` is inhabited and changes the world, which is the point: a contract
whose receive relation is empty proves nothing about receive.
-/
def liveSteps : ChannelSteps serverTopology () ServerMessage ServerWorld where
  Send := fun _ occurrence before after =>
    occurrence.1 = wire ∧ before = quiet ∧ after = quiet
  Receive := fun _ occurrence before after =>
    occurrence.1 = wire ∧ before = quiet ∧ after = afterDelivery

/-! ## The assertions, each reading exactly the fragments it is allowed to -/

/-- The session is accepting sends. -/
noncomputable def sessionOpen (session : serverTopology.ChannelId ()) :
    NetworkAssertion serverAgreement where
  holds := fun network => (network.sessions () session).status = .open
  footprint := fun fragment => fragment = .session () session
  framed := by
    intro left right agrees
    have same : left.sessions () session = right.sessions () session := agrees _ rfl
    rw [same]

/-- This occurrence has not been resolved on its session. -/
noncomputable def escrowUnresolved (session : serverTopology.ChannelId ())
    (occurrence : EdgeOccurrence serverTopology World.serverMessage ()) :
    NetworkAssertion serverAgreement where
  holds := fun network => (network.inFlight () session).resolution occurrence = none
  footprint := fun fragment => fragment = .escrow () session
  framed := by
    intro left right agrees
    have same : left.inFlight () session = right.inFlight () session := agrees _ rfl
    rw [same]

/-- The receiver has consumed this many occurrences here. -/
noncomputable def receiverAt (session : serverTopology.ChannelId ()) (count : Nat) :
    NetworkAssertion serverAgreement where
  holds := fun network => (network.sessions () session).delivered = count
  footprint := fun fragment => fragment = .session () session
  framed := by
    intro left right agrees
    have same : left.sessions () session = right.sessions () session := agrees _ rfl
    rw [same]

/-- An assertion that reads nothing. -/
noncomputable def trivialAssertion : NetworkAssertion serverAgreement :=
  NetworkAssertion.pure True

/-! ## The contract -/

noncomputable def liveChannel :
    ChannelContract () ServerMessage serverAgreement liveSteps where
  senderOutput := serverSenderOutput
  receiverInput := serverReceiverInput
  SessionOpen := sessionOpen
  SendPre := fun _ => trivialAssertion
  SenderPost := fun _ _ => trivialAssertion
  Escrow := fun message occurrence => escrowUnresolved occurrence.1 ⟨message, occurrence⟩
  ReceiverPre := fun _ occurrence => receiverAt occurrence.1 0
  ReceiverPost := fun _ occurrence => receiverAt occurrence.1 1
  escrowLocal := fun _ _ _ inFootprint => Or.inl inFootprint
  receiverPreLocal := fun _ _ _ inFootprint => Or.inl inFootprint
  sessionLocal := fun _ _ inFootprint => inFootprint
  sendOnOpenSession := by
    rintro _ occurrence before after ⟨isWire, rfl, _⟩
    rw [isWire]
    rfl
  send := by
    rintro _ occurrence before after ⟨_, rfl, rfl⟩ _ _
    exact ⟨trivial, rfl⟩
  receive := by
    rintro _ occurrence before after ⟨isWire, rfl, rfl⟩ _ _
    rw [isWire]
    rfl

/-! ## The triples do something -/

/--
**Receive advances the cursor.**

The postcondition is false at the pre-state and true at the post-state, so this
is a fact about a step. `receive_from_conjunction` takes it from
`ReceiverPre * Escrow`, which is §3's precondition and not a plain conjunction.
-/
theorem receive_advances_the_cursor (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message)
    (onWire : occurrence.1 = wire)
    (held : (liveChannel.receivePrecondition message occurrence).holds quiet) :
    (liveChannel.ReceiverPost message occurrence).holds afterDelivery :=
  liveChannel.receive_from_conjunction message occurrence ⟨onWire, rfl, rfl⟩ held

/-- And the postcondition genuinely did not hold before the step. -/
theorem cursor_had_not_advanced (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message) :
    ¬ (liveChannel.ReceiverPost message occurrence).holds quiet := by
  intro advanced
  have counted : (0 : Nat) = 1 := advanced
  exact absurd counted (by decide)

/-- The precondition is satisfiable at `quiet`, so the theorem above is not empty. -/
theorem receive_precondition_holds (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message) :
    (liveChannel.receivePrecondition message occurrence).holds quiet :=
  ⟨rfl, rfl⟩

/--
**A send happens on an open session, and the caller proves nothing.**

`sendOnOpenSession` is what makes this a demand rather than a conditional. An
earlier revision of the module took the open session as a hypothesis of `send`,
under which a contract could set `SessionOpen` to a never-satisfiable assertion,
satisfy `sessionLocal` vacuously with an empty footprint, and discharge `send`
for free while sends genuinely occurred.
-/
theorem sends_cannot_happen_on_a_closed_session (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message)
    {before after : ServerWorld}
    (stepped : liveSteps.Send message occurrence before after) :
    (liveChannel.SessionOpen occurrence.1).holds before :=
  liveChannel.sendOnOpenSession message occurrence before after stepped

/-- And a send establishes the escrow, with no session hypothesis supplied. -/
theorem send_establishes_the_escrow (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message)
    {before after : ServerWorld}
    (stepped : liveSteps.Send message occurrence before after) :
    (liveChannel.Escrow message occurrence).holds after :=
  (liveChannel.send_needs_an_open_session message occurrence stepped trivial).2

/-! ## What the discipline buys -/

/--
**`ReceiverPre * Escrow` is formable at a real contract.**

Derived from the two footprint bounds, and the reason
`Grass/Process/Network/Assertion.lean` gives `escrow` and `session` separate
constructors: with one fragment covering both, these would overlap and §3's
conjunction would not exist.
-/
theorem receiver_and_escrow_are_separate (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message) :
    NetworkAssertion.Separate
      (liveChannel.ReceiverPre message occurrence)
      (liveChannel.Escrow message occurrence) :=
  liveChannel.receiverPre_separate_from_escrow message occurrence

/--
**A step that leaves this session's ledger alone preserves the escrow.**

Accepting a connection writes a shared region. Note what this does *not* cover,
which the module note is explicit about: a second send on the same session
changes that session's ledger, so it is outside this theorem's scope and is
`Grass/Process/Network/Escrow.lean`'s `LedgerExtends` instead.
-/
theorem escrow_survives_an_unrelated_step (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message)
    (held : (liveChannel.Escrow message occurrence).holds quiet) :
    (liveChannel.Escrow message occurrence).holds afterAccept :=
  liveChannel.escrow_survives_unrelated_steps message occurrence
    (scope := fun fragment => fragment = .region .acceptCount)
    (by intro isEscrow; exact absurd isEscrow (by simp))
    (by intro isNominals; exact absurd isNominals (by simp))
    (fun fragment outside => by
      cases fragment with
      | region region =>
        cases region
        · rfl
        · exact absurd rfl outside
      | _ => rfl)
    held

/-- The hypothesis is satisfiable, so that theorem is not empty either. -/
theorem escrow_holds_at_quiet (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message) :
    (liveChannel.Escrow message occurrence).holds quiet := rfl

/-! ## And what it forbids -/

/-- An escrow assertion that reads a shared region rather than its own ledger. -/
noncomputable def escrowReadingARegion : NetworkAssertion serverAgreement where
  holds := fun network => network.shared .acceptCount = ⟨0⟩
  footprint := fun fragment => fragment = .region .acceptCount
  framed := by
    intro left right agrees
    have same : left.shared .acceptCount = right.shared .acceptCount := agrees _ rfl
    rw [same]

/--
**No contract can use it as its `Escrow`.**

`escrowLocal` is a checkable bound on an assertion the author supplies, so this
is rejected at the contract rather than at whatever later proof would have
needed the escrow to be stable. Stated over an arbitrary contract on this edge,
because it is a property of the type and not of `liveChannel`.
-/
theorem escrow_reading_a_region_is_impossible
    (steps : ChannelSteps serverTopology () ServerMessage ServerWorld)
    (contract : ChannelContract () ServerMessage serverAgreement steps)
    (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message)
    (misuses : contract.Escrow message occurrence = escrowReadingARegion) :
    False := by
  have inFootprint : (contract.Escrow message occurrence).footprint
      (.region .acceptCount) := by
    rw [misuses]
    rfl
  rcases contract.escrowLocal message occurrence (.region .acceptCount) inFootprint with
    isEscrow | isNominals
  · exact absurd isEscrow (by simp)
  · exact absurd isNominals (by simp)

/-- A delivered message settles none of the receiver's own demands. -/
theorem delivery_settles_nothing (message : ServerMessage) :
    (liveChannel.receiverInput.arrives message).settles = none :=
  liveChannel.delivery_settles_nothing message

end Grass.Process.Tests.Channel
