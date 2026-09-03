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

`liveChannel` below sends and receives. Its send takes `quiet` to a world that
actually holds the message, and its receive takes *that* world to
`afterDelivery`, consumes `ReceiverPre * Escrow`, and establishes a
`ReceiverPost` that is false before the step and true after — so
`receive_advances_the_cursor` is a fact about a state change and not about an
empty relation.

Both of those corrections came from `ProcessPlan.escrowImpliesOutstanding`.
Before it, the contract's `Escrow` assertion was "this occurrence is
unresolved", which holds at an *empty* ledger — so `Send` could take `quiet` to
`quiet` and satisfy its postcondition, and the receive's precondition was
satisfiable at a world where nothing had been sent. Two vacuous laws, both
invisible until something outside the contract said what escrow means.

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

open Classical in
/-- The ledger holding exactly one occurrence, in flight. -/
noncomputable def holding (occurrence : EdgeOccurrence serverTopology World.serverMessage ()) :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [occurrence]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by simp

open Classical in
/--
The world a send of one occurrence on the wire reaches.

An earlier version of `liveSteps.Send` had `after = quiet` — a send that put
nothing in flight. It went unnoticed because the contract's `Escrow` assertion
was `resolution = none`, which holds at an empty ledger, so the postcondition
was satisfied by a world where nothing had been sent.

`ProcessPlan.escrowImpliesOutstanding` is what made both visible: it requires
`EscrowLedger.Outstanding`, which is created-membership *and* unresolvedness,
and neither the old assertion nor the old after-world could supply the first.
-/
noncomputable def afterSend (occurrence : EdgeOccurrence serverTopology World.serverMessage ()) :
    ServerWorld :=
  { quiet with
      inFlight := fun _ session =>
        if session = wire then holding occurrence else EscrowLedger.empty }

theorem afterSend_wire (occurrence : EdgeOccurrence serverTopology World.serverMessage ()) :
    (afterSend occurrence).inFlight () wire = holding occurrence := by
  simp [afterSend]

/--
The step relations.

Both are inhabited and both change the world, which is the point: a contract
whose relations are empty, or whose send goes nowhere, proves nothing.
-/
def liveSteps : ChannelSteps serverTopology () ServerMessage ServerWorld where
  Send := fun message occurrence before after =>
    occurrence.1 = wire ∧ before = quiet ∧ after = afterSend ⟨message, occurrence⟩
  Receive := fun message occurrence before after =>
    occurrence.1 = wire ∧ before = afterSend ⟨message, occurrence⟩ ∧
      after = afterDelivery

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

/--
This occurrence is escrowed on its session and not yet resolved.

Both conjuncts, because `ProcessPlan.escrowImpliesOutstanding` requires
`EscrowLedger.Outstanding`, which is created-membership *and* unresolvedness. An
earlier version of this assertion had only the second, so a contract could claim
escrow for an occurrence the ledger never created — `Grass/Process/Bag.lean`'s
"fabricated" at the channel seam. Adding the plan-level tie is what made the
fixture's own assertion visibly too weak.
-/
noncomputable def escrowUnresolved (session : serverTopology.ChannelId ())
    (occurrence : EdgeOccurrence serverTopology World.serverMessage ()) :
    NetworkAssertion serverAgreement where
  holds := fun network => (network.inFlight () session).Outstanding occurrence
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
    rintro message occurrence before after ⟨isWire, rfl, rfl⟩ _ _
    refine ⟨trivial, ?_⟩
    show ((afterSend ⟨message, occurrence⟩).inFlight () occurrence.1).Outstanding
      ⟨message, occurrence⟩
    rw [isWire, afterSend_wire]
    exact ⟨List.mem_cons_self, rfl⟩
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
    (held : (liveChannel.receivePrecondition message occurrence).holds
      (afterSend ⟨message, occurrence⟩)) :
    (liveChannel.ReceiverPost message occurrence).holds afterDelivery :=
  liveChannel.receive_from_conjunction message occurrence ⟨onWire, rfl, rfl⟩ held

/-- And the postcondition genuinely did not hold before the step. -/
theorem cursor_had_not_advanced (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message) :
    ¬ (liveChannel.ReceiverPost message occurrence).holds quiet := by
  intro advanced
  have counted : (0 : Nat) = 1 := advanced
  exact absurd counted (by decide)

/--
The hypothesis is satisfiable, so that theorem is not empty either — at the
world a send actually reaches.

It used to be stated at `quiet`, where nothing has been sent. That was provable
only because the contract's escrow assertion did not require the occurrence to
have been created.
-/
theorem escrow_holds_after_a_send (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message)
    (onWire : occurrence.1 = wire) :
    (liveChannel.Escrow message occurrence).holds (afterSend ⟨message, occurrence⟩) := by
  show ((afterSend ⟨message, occurrence⟩).inFlight () occurrence.1).Outstanding
    ⟨message, occurrence⟩
  rw [onWire, afterSend_wire]
  exact ⟨List.mem_cons_self, rfl⟩

/-- The precondition is satisfiable at `quiet`, so the theorem above is not empty. -/
theorem receive_precondition_holds (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message)
    (onWire : occurrence.1 = wire) :
    (liveChannel.receivePrecondition message occurrence).holds
      (afterSend ⟨message, occurrence⟩) :=
  ⟨rfl, escrow_holds_after_a_send message occurrence onWire⟩

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
