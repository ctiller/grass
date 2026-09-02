import Grass.Process.Network.Channel
import Tests.Process.WorldFixtures

/-!
# A channel contract you can build, and one you cannot

`Grass/Process/Network/Channel.lean` replaces four of `docs/PROCESS.md` §3's
opaque law fields with a footprint discipline and derives the laws. That trade
is only worth making if the discipline is (a) satisfiable by a real contract and
(b) genuinely restrictive. This file is both halves.

* `serverChannel` is a contract at the M2 fixture topology, over the canonical
  `logicalWorldAgreement` rather than an invented world. Its escrow reads the
  escrow ledger of its own session; its receiver precondition reads that
  session's status; and both `escrowLocal` and `receiverPreLocal` discharge.
* `escrow_reading_a_region_is_impossible` is the teeth. An escrow assertion that
  reads a shared region cannot be a contract's `Escrow`, because `escrowLocal`
  is unsatisfiable for it. That is what an opaque `escrowStable` field could not
  have said.
* `receiver_and_escrow_are_separate` is §3's `ReceiverPre * Escrow` formable at a
  concrete contract, and `escrow_survives_an_unrelated_step` is "unrelated
  transitions must preserve `Escrow`" at a concrete step — both derived, neither
  assumed.
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

/-- A send discharges the listener's `log` demand. -/
def serverSenderOutput :
    SenderDemandEmbedding serverTopology .listener ServerMessage where
  emits := fun _ => .log

/-- And arrives at the connection as external entropy, settling nothing. -/
def serverReceiverInput :
    ReceiverEventEmbedding serverTopology .connection ServerMessage where
  arrives := fun _ => .external .wake
  arrivesUnsettled := fun _ => rfl

/-- The step relations. This fixture is about the contract, not the family. -/
def serverSteps : ChannelSteps serverTopology () ServerMessage ServerWorld where
  Send := fun _ occurrence before after =>
    before = quiet ∧ after = quiet ∧ occurrence.1 = wire
  Receive := fun _ _ _ _ => False

/-! ## The assertions, each reading exactly its own fragment -/

/-- The session is accepting sends. -/
noncomputable def sessionOpen (session : serverTopology.ChannelId ()) :
    NetworkAssertion serverAgreement where
  holds := fun network => network.sessions () session = .open
  footprint := fun fragment => fragment = .session () session
  framed := by
    intro left right agrees
    have same : left.sessions () session = right.sessions () session := agrees _ rfl
    rw [same]

/-- The channel holds nothing that has not been resolved. -/
noncomputable def escrowHolds (session : serverTopology.ChannelId ()) :
    NetworkAssertion serverAgreement where
  holds := fun network => (network.inFlight () session).outstanding = []
  footprint := fun fragment => fragment = .escrow () session
  framed := by
    intro left right agrees
    have same : left.inFlight () session = right.inFlight () session := agrees _ rfl
    rw [same]

/-- The receiver's cursor: this fixture reads the session's status for it. -/
noncomputable def receiverAt (session : serverTopology.ChannelId ()) :
    NetworkAssertion serverAgreement where
  holds := fun network => network.sessions () session ≠ .died
  footprint := fun fragment => fragment = .session () session
  framed := by
    intro left right agrees
    have same : left.sessions () session = right.sessions () session := agrees _ rfl
    rw [same]

/-- An assertion that reads nothing, for the sender's postcondition. -/
noncomputable def senderDone : NetworkAssertion serverAgreement :=
  NetworkAssertion.pure True

/-! ## The contract -/

noncomputable def serverChannel :
    ChannelContract () ServerMessage serverAgreement serverSteps where
  senderOutput := serverSenderOutput
  receiverInput := serverReceiverInput
  SessionOpen := sessionOpen
  SendPre := fun _ => senderDone
  SenderPost := fun _ _ => senderDone
  Escrow := fun _ occurrence => escrowHolds occurrence.1
  ReceiverPre := fun _ occurrence => receiverAt occurrence.1
  ReceiverPost := fun _ _ => senderDone
  escrowLocal := fun _ _ _ inFootprint => inFootprint
  receiverPreLocal := fun _ _ _ inFootprint => inFootprint
  sessionLocal := fun _ _ inFootprint => inFootprint
  send := by
    rintro _ occurrence before after ⟨rfl, rfl, _⟩ _ _
    exact ⟨trivial, rfl⟩
  receive := by
    rintro _ _ _ _ ⟨⟩

/-! ## What the discipline buys -/

/--
**`ReceiverPre * Escrow` is formable at a real contract.**

`docs/PROCESS.md` §3 writes `receive`'s precondition as that separating
conjunction. It is a theorem here rather than a field, derived from the two
footprint bounds, and it is the reason `NetworkFragment` splits `escrow` from
`session`: with one constructor covering both, these two would overlap and the
conjunction would not exist.
-/
theorem receiver_and_escrow_are_separate (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message) :
    NetworkAssertion.Separate
      (serverChannel.ReceiverPre message occurrence)
      (serverChannel.Escrow message occurrence) :=
  serverChannel.receiverPre_separate_from_escrow message occurrence

/--
**Unrelated transitions preserve the escrow.**

§3's "buffered delay is sound", at a concrete step: accepting a connection
writes a shared region and leaves this session's escrow alone, so the escrow
assertion survives with no re-proof. Derived from `escrowLocal` and the frame
rule, not asserted by a field.
-/
theorem escrow_survives_an_unrelated_step (message : ServerMessage)
    (occurrence : serverTopology.ChannelOccurrence () message)
    (held : (serverChannel.Escrow message occurrence).holds quiet) :
    (serverChannel.Escrow message occurrence).holds afterAccept :=
  serverChannel.escrow_survives_unrelated_steps message occurrence
    (scope := fun fragment => fragment = .region .acceptCount)
    (by
      intro isEscrow
      exact absurd isEscrow (by simp))
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

The teeth. `escrowLocal` is a checkable bound on an assertion the author
supplies, so an escrow that reads a shared region is rejected at the contract
rather than at whatever later proof would have needed it to be stable. An opaque
`escrowStable : StableUnderUnrelatedProcessSteps Escrow` field could not have
rejected it: nothing would check that the supplied value was one.

Stated over an arbitrary contract on this edge, not just `serverChannel`,
because it is a property of the type.
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
  have isEscrow :=
    contract.escrowLocal message occurrence (.region .acceptCount) inFootprint
  exact absurd isEscrow (by simp)

/-- A message settles none of the receiver's own demands. -/
theorem delivery_settles_nothing (message : ServerMessage) :
    (serverChannel.receiverInput.arrives message).settles = none :=
  serverChannel.message_is_routed message

end Grass.Process.Tests.Channel
