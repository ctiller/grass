import Grass.Process.Network.Assertion
import Grass.Process.Network.Escrow

/-!
# Channel contracts

`docs/PROCESS.md` §3, on what a channel contract is for:

> Channel contracts therefore give process basic blocks their entry and exit
> conditions. A process transition may be authored as arbitrary assembly, a
> standard driver path, or a proved macro; its local proof ends at
> `SenderPost * Escrow` or begins at `ReceiverPre * Escrow`. It need not reopen
> the whole network invariant.

and on the object at the centre of it:

> `SendPre` is the sender's exit condition for the communication edge. `Escrow`
> contains only the transferred payload and affine resolve token. `ReceiverPre`
> owns the receiver's independently evolving local/session cursor. Receive
> consumes `ReceiverPre * Escrow` and establishes `ReceiverPost`; the sender
> never fabricates receiver state.

## Three opaque laws replaced, four deferred to named owners

`docs/PROCESS.md` §3 declares `ChannelContract` with seventeen fields, seven of
them opaque law names — `escrowStable`, `prefixConservation`,
`atMostOneResolution`, `resolutions`, `transferExact`, `session`, `frame` — each
typed by a name the corpus declares nowhere.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` standing risk 2 records the count; the
sharper problem is that an opaque field of an undeclared type is a promise
nothing checks, and an author discharges it by writing anything at all.

This structure has fourteen fields. **Three** of the seven — `escrowStable`,
`session` and `frame` — are replaced by a *footprint discipline*: `escrowLocal`,
`receiverPreLocal` and `sessionLocal` bound what the author's own assertions may
read, `sendOnOpenSession` makes the session law a demand rather than a
conditional, and from those:

* `escrow_survives_unrelated_steps` and `frame_unmentioned` are
  `frame_of_disjoint_scope`.
* `receiverPre_separate_from_escrow` is why `escrow` and `session` are separate
  `NetworkFragment` constructors: §3 requires `ReceiverPre * Escrow` to be
  *formable*, and with one fragment covering both it would not be.
* `receivePrecondition` builds that conjunction, so `receive`'s precondition is
  the separating conjunction §3 writes rather than a plain one.

The other **four** are not fields here at all, and are deferred to owners this
note names rather than dropped. `prefixConservation` and `atMostOneResolution`
are `Grass/Process/Network/Escrow.lean`'s, proved there over the ledger, and a
contract cannot restate them because it cannot see a ledger through an abstract
agreement. `resolutions` and `transferExact` quantify over the transition
family, which is `Transition.lean`'s. `ChannelSteps` below is the seam that lets
the contract be written first: it takes its send and receive relations as
parameters, and the family instantiates them.

## What `escrow_survives_unrelated_steps` does and does not cover

It covers steps that leave this session's escrow *ledger* untouched, which is
weaker than §3's "unrelated transitions must preserve `Escrow`; this makes
buffered delay sound". A second send on the *same* session, or a resolution of a
different occurrence on it, changes that ledger, so this theorem says nothing
about them — and those are exactly the buffered-delay cases.

That is a consequence of fragment granularity rather than an error in the
theorem: the escrow fragment is per session, the world holds one ledger per
session, and no finer scope exists to be disjoint from. The same-session case is
`Grass/Process/Network/Escrow.lean`'s, where `LedgerExtends` gives
`resolvedStaysResolved`, `noLoss` and `settled_monotone` across any number of
intervening sends and resolutions. An earlier revision of this note claimed this
theorem was §3's sentence outright; it is one half of it.

## Why the world stays abstract here

`docs/PROCESS.md` §3, after decision 128: "A reusable lower module may quantify
over an arbitrary `WorldAgreement`; the completed plan always instantiates its
channel contracts at the full logical network." This is that lower module. It
therefore cannot say "the session is open" by projecting a field — there is no
field to project — so the session law is an *assertion the contract supplies*,
`SessionOpen`, with its footprint bounded to the session fragment. A plan
instantiates it at the real predicate on `LogicalProcessNetworkCore.sessions`.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r x msg

/--
Which of the sender's demands a message discharges.

`docs/PROCESS.md` §3's `SenderDemandEmbedding`. The corpus names it and gives no
fields, so this is the minimum that makes a send *mean* something at the
sender's protocol: without it a channel would move payloads with no relation to
the sending process's own obligations, and the send would discharge nothing.
-/
structure SenderDemandEmbedding {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary)
    (sender : topology.ProcessKind) (Message : Type msg) where
  /-- The demand this message realizes. -/
  emits : Message → (topology.protocol sender).Demand

/--
How a message arrives at the receiver.

`docs/PROCESS.md` §3's `ReceiverEventEmbedding`, with the one law the corpus does
determine.
-/
structure ReceiverEventEmbedding {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary)
    (receiver : topology.ProcessKind) (Message : Type msg) where
  /-- The event the receiver sees. -/
  arrives : Message → (topology.protocol receiver).Event
  /--
  **A delivered message answers none of the receiver's own demands.**

  A channel message is an external input. Settling one of the receiver's
  outstanding demands is what `Grass/Process/Network/Child.lean`'s
  `ChildDemandBinding` does, and it does it through a binding that proves the
  answer belongs to that demand. Without this law a channel could deliver an
  event that claimed to settle a demand nothing authorized it to settle, which
  is the cross-wiring `docs/PROCESS.md` §5 forbids when it says a driver may not
  "attach one result to another occurrence".
  -/
  arrivesUnsettled : ∀ message, (arrives message).settles = none

/--
The send and receive relations a contract is stated over.

Parameters rather than fields, because the transition family that supplies them
is `Grass/Process/Network/Transition.lean`'s and a contract has to be writable
first. This is the same seam `docs/DECISIONS.md` decision 128 used for the world.
-/
structure ChannelSteps {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary)
    (edge : topology.ChannelKind) (Message : Type msg) (World : Type x) where
  /-- A send of this message that created this occurrence. -/
  Send : (message : Message) → topology.ChannelOccurrence edge message →
    World → World → Prop
  /-- A receive of that exact occurrence. -/
  Receive : (message : Message) → topology.ChannelOccurrence edge message →
    World → World → Prop

/--
A Hoare triple over one step relation.

`docs/PROCESS.md` §3's `HoareTransition`: if the step happens and the
precondition held before, the postcondition holds after.
-/
def HoareTransition {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
    {World : Type x} {agreement : WorldAgreement topology World}
    (Step : World → World → Prop)
    (pre post : NetworkAssertion agreement) : Prop :=
  ∀ before after, Step before after → pre.holds before → post.holds after

/--
The contract on one channel edge.

Fourteen fields where `docs/PROCESS.md` §3 declares seventeen; see the module
note for which three opaque laws became theorems and where the other four
went.
-/
structure ChannelContract {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
    (edge : topology.ChannelKind) (Message : Type msg)
    {World : Type x} (agreement : WorldAgreement topology World)
    (steps : ChannelSteps topology edge Message World) where
  /-- Which of the sender's demands each message discharges. -/
  senderOutput : SenderDemandEmbedding topology (topology.endpoints edge).1 Message
  /-- How each message arrives at the receiver. -/
  receiverInput : ReceiverEventEmbedding topology (topology.endpoints edge).2 Message
  /-- This session is accepting sends. -/
  SessionOpen : topology.ChannelId edge → NetworkAssertion agreement
  /-- The sender's exit condition for the edge. -/
  SendPre : Message → NetworkAssertion agreement
  /-- What the sender knows afterwards. -/
  SenderPost : (message : Message) →
    topology.ChannelOccurrence edge message → NetworkAssertion agreement
  /-- What the channel owns until the occurrence is resolved. -/
  Escrow : (message : Message) →
    topology.ChannelOccurrence edge message → NetworkAssertion agreement
  /-- The receiver's own cursor, evolving independently of the sender. -/
  ReceiverPre : (message : Message) →
    topology.ChannelOccurrence edge message → NetworkAssertion agreement
  /-- What the receiver establishes. -/
  ReceiverPost : (message : Message) →
    topology.ChannelOccurrence edge message → NetworkAssertion agreement
  /--
  **The escrow reads its own session's escrow fragment, or the nominal history,
  and nothing else.**

  The field that replaces `escrowStable` and half of `frame`. An opaque
  `StableUnderUnrelatedProcessSteps` is a promise; this is a checkable bound, and
  `escrow_survives_unrelated_steps` derives the promise from it.

  `nominals` is admitted because `docs/PROCESS.md` §3 says `Escrow` contains "the
  transferred payload **and affine resolve token**", and
  `Grass/Process/Network/Assertion.lean` gives `nominals` as a fragment precisely
  so that a claim about at-most-one resolution has something to read. An earlier
  revision bounded the footprint to the escrow fragment alone, which made the
  token half of §3's sentence unstatable — and left `Assertion.lean`'s stated
  reason for the `nominals` constructor unreachable from any contract.
  -/
  escrowLocal : ∀ message occurrence fragment,
    (Escrow message occurrence).footprint fragment →
    fragment = .escrow edge occurrence.1 ∨ fragment = .nominals
  /--
  **The receiver's precondition reads its own session cursor and its own local
  state, and nothing else.**

  §3: "`ReceiverPre` owns the receiver's independently evolving **local**/session
  cursor." Both halves. An earlier revision bounded it to the session fragment
  alone, which read the sentence as if `local` were not there: a contract whose
  receive depended on the receiving process's own state was unwritable, and
  three docstrings said otherwise.

  With `escrowLocal` this is still what makes `ReceiverPre * Escrow` formable,
  because neither admitted fragment is an escrow fragment.
  -/
  receiverPreLocal : ∀ message occurrence fragment,
    (ReceiverPre message occurrence).footprint fragment →
    fragment = .session edge occurrence.1 ∨
      ∃ slot, fragment = .instanceState (topology.endpoints edge).2 slot
  /-- And the session predicate reads the session fragment. -/
  sessionLocal : ∀ session fragment,
    (SessionOpen session).footprint fragment → fragment = .session edge session
  /--
  **A send happens only on an open session.**

  Without this the session law is a conditional postcondition, and a conditional
  demands nothing: an earlier revision let a contract set `SessionOpen` to a
  never-satisfiable assertion, satisfy `sessionLocal` vacuously with an empty
  footprint, and discharge `send` for free while sends genuinely occurred. That
  is the same "an opaque field is a promise" shape this module set out to
  remove, reappearing one level in.
  -/
  sendOnOpenSession : ∀ message occurrence before after,
    steps.Send message occurrence before after →
    (SessionOpen occurrence.1).holds before
  /--
  **Send.** From the sender's exit condition, and an open session, to the
  sender's postcondition conjoined with the escrow the channel now owns.

  §3's triple, with the session law folded into the precondition because this
  layer cannot project a session status from an abstract world.
  -/
  send : ∀ message occurrence before after,
    steps.Send message occurrence before after →
    (SendPre message).holds before →
    (SessionOpen occurrence.1).holds before →
    (SenderPost message occurrence).holds after ∧
      (Escrow message occurrence).holds after
  /--
  **Receive.** Consumes `ReceiverPre * Escrow` and establishes `ReceiverPost`.

  §3: "the sender never fabricates receiver state", which is why the
  precondition names the receiver's own cursor rather than anything the sender
  established.
  -/
  receive : ∀ message occurrence before after,
    steps.Receive message occurrence before after →
    (ReceiverPre message occurrence).holds before →
    (Escrow message occurrence).holds before →
    (ReceiverPost message occurrence).holds after

namespace ChannelContract

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
  {edge : topology.ChannelKind} {Message : Type msg}
  {World : Type x} {agreement : WorldAgreement topology World}
  {steps : ChannelSteps topology edge Message World}
  (contract : ChannelContract edge Message agreement steps)

/-! ## The laws the footprint discipline buys -/

/--
**Unrelated transitions preserve the escrow.**

`docs/PROCESS.md` §3: "Unrelated transitions must preserve `Escrow`; this makes
buffered delay sound." A field named `escrowStable` would have asserted it; this
proves it, from `escrowLocal` and `Grass/Process/Network/Assertion.lean`'s frame
rule.

"Unrelated" is exactly §8's `Disjoint (TransitionScope step) Scope`: a scope not
containing this session's escrow fragment.
-/
theorem escrow_survives_unrelated_steps (message : Message)
    (occurrence : topology.ChannelOccurrence edge message)
    (scope : NetworkFragment topology → Prop)
    (unrelated : ¬ scope (.escrow edge occurrence.1))
    (nominalsUntouched : ¬ scope .nominals)
    {before after : World}
    (touchesOnly : ∀ fragment, ¬ scope fragment →
      agreement.Agrees fragment before after)
    (held : (contract.Escrow message occurrence).holds before) :
    (contract.Escrow message occurrence).holds after :=
  (contract.Escrow message occurrence).frame_of_disjoint_scope scope
    (fun fragment inScope inFootprint => by
      rcases contract.escrowLocal message occurrence fragment inFootprint with
        isEscrow | isNominals
      · exact unrelated (isEscrow ▸ inScope)
      · exact nominalsUntouched (isNominals ▸ inScope))
    touchesOnly held

/--
**And the receiver's cursor survives everything that does not touch it.**

The other half of §3's `frame : UnmentionedProcessesAndRegionsPreserved`. A step
confined to the sender's fragments — or to any scope avoiding this session — does
not disturb the receiver's precondition, which is what lets a receive be checked
without reopening the network invariant.
-/
theorem frame_unmentioned (message : Message)
    (occurrence : topology.ChannelOccurrence edge message)
    (scope : NetworkFragment topology → Prop)
    (unrelated : ¬ scope (.session edge occurrence.1))
    (receiverUntouched : ∀ slot,
      ¬ scope (.instanceState (topology.endpoints edge).2 slot))
    {before after : World}
    (touchesOnly : ∀ fragment, ¬ scope fragment →
      agreement.Agrees fragment before after)
    (held : (contract.ReceiverPre message occurrence).holds before) :
    (contract.ReceiverPre message occurrence).holds after :=
  (contract.ReceiverPre message occurrence).frame_of_disjoint_scope scope
    (fun fragment inScope inFootprint => by
      rcases contract.receiverPreLocal message occurrence fragment inFootprint with
        isSession | ⟨slot, isSlot⟩
      · exact unrelated (isSession ▸ inScope)
      · exact receiverUntouched slot (isSlot ▸ inScope))
    touchesOnly held

/--
**`ReceiverPre` and `Escrow` are separate.**

The theorem `docs/PROCESS.md` §3 needs in order to write
`ReceiverPre message occurrence * Escrow message occurrence` at all, and the
reason `Grass/Process/Network/Assertion.lean` gives `escrow` and `session`
separate constructors: with a single fragment covering both the escrowed payload
and the receiver's cursor, these two would overlap, `Separate` would be false,
and the conjunction §3 requires would be unformable.
-/
theorem receiverPre_separate_from_escrow (message : Message)
    (occurrence : topology.ChannelOccurrence edge message) :
    NetworkAssertion.Separate
      (contract.ReceiverPre message occurrence)
      (contract.Escrow message occurrence) := by
  intro fragment inReceiver inEscrow
  rcases contract.receiverPreLocal message occurrence fragment inReceiver with
    isSession | ⟨_, isSlot⟩ <;>
    rcases contract.escrowLocal message occurrence fragment inEscrow with
      isEscrow | isNominals
  · rw [isSession] at isEscrow; exact absurd isEscrow (by simp)
  · rw [isSession] at isNominals; exact absurd isNominals (by simp)
  · rw [isSlot] at isEscrow; exact absurd isEscrow (by simp)
  · rw [isSlot] at isNominals; exact absurd isNominals (by simp)

/-- So the separating conjunction exists. This is `receive`'s real precondition. -/
def receivePrecondition (message : Message)
    (occurrence : topology.ChannelOccurrence edge message) :
    NetworkAssertion agreement :=
  (contract.ReceiverPre message occurrence).sep
    (contract.Escrow message occurrence)
    (contract.receiverPre_separate_from_escrow message occurrence)

/-- And `receive` is stated against it, which is §3's triple. -/
theorem receive_from_conjunction (message : Message)
    (occurrence : topology.ChannelOccurrence edge message)
    {before after : World}
    (stepped : steps.Receive message occurrence before after)
    (held : (contract.receivePrecondition message occurrence).holds before) :
    (contract.ReceiverPost message occurrence).holds after :=
  contract.receive message occurrence before after stepped held.1 held.2

/--
**Send establishes `SenderPost * Escrow`.**

§3 writes the send triple's postcondition as a separating conjunction. It is one
here only when the sender's postcondition avoids the escrow fragment, which is a
property of the contract's own choice of `SenderPost` rather than something this
module can assume — so it is a hypothesis, and `send_establishes_conjunction`
says what follows when it holds.
-/
theorem send_establishes_conjunction (message : Message)
    (occurrence : topology.ChannelOccurrence edge message)
    (senderAvoidsEscrow : ¬ (contract.SenderPost message occurrence).footprint
      (.escrow edge occurrence.1))
    (senderAvoidsNominals :
      ¬ (contract.SenderPost message occurrence).footprint .nominals)
    {before after : World}
    (stepped : steps.Send message occurrence before after)
    (sendPre : (contract.SendPre message).holds before)
    (sessionOpen : (contract.SessionOpen occurrence.1).holds before) :
    ((contract.SenderPost message occurrence).sep
      (contract.Escrow message occurrence)
      (fun fragment inSender inEscrow => by
        rcases contract.escrowLocal message occurrence fragment inEscrow with
          isEscrow | isNominals
        · exact senderAvoidsEscrow (isEscrow ▸ inSender)
        · exact senderAvoidsNominals (isNominals ▸ inSender))).holds
      after :=
  contract.send message occurrence before after stepped sendPre sessionOpen

/--
**A send happens on an open session, and the caller need not prove it.**

`ChannelSessionLaw` in §3's field list. `SessionOpen` is a supplied assertion
rather than a projection because at this layer the world is abstract, so "open"
is whatever the plan's own predicate on `LogicalProcessNetworkCore.sessions`
says — but the *demand* is `sendOnOpenSession`, and this theorem takes it from
there rather than from a hypothesis.

An earlier revision made the session law a hypothesis of `send` alone. That
demands nothing: a contract could set `SessionOpen` to a never-satisfiable
assertion, satisfy `sessionLocal` vacuously with an empty footprint, and
discharge `send` for free while sends genuinely occurred.
-/
theorem send_needs_an_open_session (message : Message)
    (occurrence : topology.ChannelOccurrence edge message)
    {before after : World}
    (stepped : steps.Send message occurrence before after)
    (sendPre : (contract.SendPre message).holds before) :
    (contract.SessionOpen occurrence.1).holds before ∧
      (contract.Escrow message occurrence).holds after :=
  ⟨contract.sendOnOpenSession message occurrence before after stepped,
    (contract.send message occurrence before after stepped sendPre
      (contract.sendOnOpenSession message occurrence before after stepped)).2⟩

/-- A delivered message settles none of the receiver's own demands. -/
theorem delivery_settles_nothing (message : Message) :
    (contract.receiverInput.arrives message).settles = none :=
  contract.receiverInput.arrivesUnsettled message

end ChannelContract

end Grass.Process
