import Grass.Process.Network.Channel
import Grass.Process.Network.World

/-!
# The process plan

`docs/PROCESS.md` §3, as amended by `docs/DECISIONS.md` decision 128:

```text
structure ProcessPlan (registry : ProtocolRegistry) (boundary : DriverBoundary)
    extends ProcessTopology registry boundary where
  Message : ChannelKind -> Type
  channel : (edge : ChannelKind) ->
    ChannelContract toProcessTopology (Message edge)
      (logicalWorldAgreement toProcessTopology Message) edge
  boundaryProjection : RootLocalDemandProjection toProcessTopology boundary

abbrev LogicalProcessNetwork (plan : ProcessPlan registry boundary) :=
  LogicalProcessNetworkCore plan.toProcessTopology plan.Message
```

This module closes the loop decision 128 opened. `Grass/Process/Network/World.lean`
built the carrier from a topology and a message family;
`Grass/Process/Network/Channel.lean` stated contracts over an arbitrary
agreement; here the plan declares its message family, instantiates its contracts
at the canonical agreement for the full network, and `LogicalProcessNetwork` is
the public name for the world it steps through.

§3 is explicit that the abbreviation is the public one: "`LogicalProcessNetworkCore`
is a construction dependency, not a second public network semantics; authors and
later theorems use `LogicalProcessNetwork plan`."

## `steps` is a field, and the transition family will constrain it

`ChannelContract` takes its send and receive relations as a parameter, because
`Grass/Process/Network/Transition.lean` does not exist yet. A plan therefore
carries them. That is not a permanent shape: when the transition family lands,
`NetworkTransition.send` and `.receive` become the relations, and the plan's
`steps` field becomes a *derived* value rather than a supplied one. The field is
where that obligation lives until then, and it is written down here rather than
remembered.

## `boundaryProjection` is derived, not declared

§3 declares it twice, and this module takes the older one. `ProcessGraph` already
carries `rootBoundary : ProtocolExposesBoundary (protocol root) boundary`, which
is a partial map from the root protocol's demands into the boundary's — exactly
"selected root-local demands, with the nested and flattened ones staying
private". `ProcessPlan.boundaryProjection : RootLocalDemandProjection` would be a
second object with the same job, which is the defect class
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.1 already found once.

`RootLocalDemandProjection` below is therefore a *definition* over the graph's
exposure, not a field. One caveat is recorded rather than hidden: §3 describes
the projection as running "from selected root-local **occurrences** to
`DriverBoundary` occurrences", and this layer's outstanding demands are a
`Grass/Process/Bag.lean` multiset with multiplicities but no identities, so an
occurrence-level projection is not statable here at all. §10.15 files that.

## Well-formedness is the world's, for now

`Sound` below is a named wrapper around `LogicalProcessNetworkCore.WellFormed`
and adds nothing yet. That is deliberate rather than an oversight: every law
this module could think of turned out to be statable one layer down, including
the reroute-landing obligation `Grass/Process/Network/Escrow.lean` records as
"dischargeable only by `Plan.lean`" — the world already holds every session's
ledger of every edge, so it is `LogicalProcessNetworkCore.ReroutesLand` there.

The clauses that genuinely need a plan need the *transition family* too: that a
step's channel transitions are the ones this plan's contracts govern, and that
escrow resolutions are the family's. `Transition.lean` adds them to `Sound`.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

set_option linter.checkUnivs false in
/--
A plan: a topology, the message family its channels carry, and a contract for
every edge.

`Obligations` is a field rather than a global type for the reason
`Grass/Process/Network/World.lean` gives: the obligation ledger belongs to the
memory layer, and `Grass.Process` importing it to state its own world is the
edge `coord1:5`'s diamond exists to prevent. A plan chooses it, and every
transition family over that plan inherits the choice.

The universe linter is disabled here for the same reason `Grass/Process/Spec.lean`
disables it: `r` and `m` — the topology's universe and the message family's —
appear only inside a `max`, because they are independent choices this structure
never has to separate. Naming a spurious parameter to satisfy the linter would
be worse than saying so, and an earlier revision did exactly that: it carried an
unused `Message : Type (m + 1)` parameter that every caller had to supply and
nothing read.
-/
structure ProcessPlan (registry : ProtocolRegistry.{u, w, v})
    (boundary : DriverBoundary.{u}) (Obligations : Type o) :
    Type (max (u + 1) (w + 1) (v + 1) (r + 1) (m + 1) (o + 1)) where
  /-- The topology this plan realizes. -/
  topology : ProcessTopologyCore.{u, w, v, r} registry boundary
  /-- What each channel edge carries. Declared before the contracts, per
  decision 128, because the world's carrier depends on it and the contracts
  depend on the world. -/
  message : topology.ChannelKind → Type m
  /-- The send and receive relations. See the module note: a field until
  `Transition.lean` supplies them. -/
  steps : (edge : topology.ChannelKind) →
    ChannelSteps topology edge (message edge)
      (LogicalProcessNetworkCore topology message Obligations)
  /-- The contract on each edge, at the canonical agreement for the full
  network. -/
  channel : (edge : topology.ChannelKind) →
    ChannelContract edge (message edge)
      (logicalWorldAgreement topology message Obligations) (steps edge)
  /--
  **And a contract's "open session" is the session the network records as open.**

  `ChannelContract.sendOnOpenSession` makes the session law a *demand* rather
  than a promise, and `sessionLocal` bounds what the assertion may read — but
  neither says what it *means*, and `ChannelContract`'s world is an abstract
  `World` with no sessions to mean it against. So a contract could set
  `SessionOpen` to an assertion holding everywhere, satisfy both, and admit
  sends on a session `channelClose` or `channelDeath` had already shut.

  A plan's world is `LogicalProcessNetworkCore`, which does have a status, so
  the tie belongs here. It could not be made at all until
  `Grass/Process/Network/Transition.lean`'s `ClosesSession` and `KillsSession`
  existed: `SessionStatus.closed` and `.died` were producible by nothing, so
  there was no status for the assertion to be tied to.

  `no_send_on_a_closed_session` is what it buys.

  An implication rather than an equivalence, for the reason the next field gives
  for itself. This was an `↔` and only `.mp` was ever used; the `←` direction
  pins `SessionOpen` to *exactly* the status, so no contract could require
  anything more of a session before a send — not a handshake, not a capability,
  not a condition on the receiver's cursor, which `sessionLocal` explicitly
  permits an author to read. Local adversarial review found the asymmetry with
  the neighbouring field, whose docstring already made the argument.
  -/
  sessionOpenIsRecorded : ∀ (edge : topology.ChannelKind) (session : topology.ChannelId edge)
    (network : LogicalProcessNetworkCore topology message Obligations),
    ((channel edge).SessionOpen session).holds network →
      (network.sessions edge session).status = .open
  /--
  **And a contract's escrow claim is escrow the ledger actually holds.**

  The same shape one field over. `ChannelContract.Escrow` is what a send's
  postcondition hands the channel, `escrowLocal` bounds what it may read, and
  nothing said what it *means* — so a contract could claim escrow for an
  occurrence the ledger never created. That is `Grass/Process/Bag.lean`'s
  "fabricated" at the channel seam.

  An implication rather than an equivalence, deliberately. `docs/PROCESS.md` §3
  puts the affine resolve token "inside `Escrow`, not a field whose Lean value
  is assumed noncopyable", so `Escrow` is *more* than outstandingness and an
  `↔` would forbid the token. What must not happen is the other direction: a
  claim with nothing behind it.

  It does not exclude every degenerate contract, and the residual escape is
  worth naming: an `Escrow` that holds *nowhere* satisfies this vacuously, and
  then `ChannelContract.send` forces `steps.Send` to be empty wherever `SendPre`
  and `SessionOpen` hold — with `sendOnOpenSession`, empty outright. Such a plan
  is degenerate rather than unsound, and nothing in `ProcessPlan` requires
  `steps.Send` to be inhabited. The same is true of the field above and of
  `ChannelContract.sendOnOpenSession` before them: a plan whose relations are
  empty satisfies every tie.
  -/
  escrowImpliesOutstanding : ∀ (edge : topology.ChannelKind) (carried : message edge)
    (occurrence : topology.ChannelOccurrence edge carried)
    (network : LogicalProcessNetworkCore topology message Obligations),
    ((channel edge).Escrow carried occurrence).holds network →
      (network.inFlight edge occurrence.1).Outstanding ⟨carried, occurrence⟩

namespace ProcessPlan

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o}
  (plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations)

/--
The world a plan steps through.

`docs/PROCESS.md` §3's public name. `LogicalProcessNetworkCore` is the
construction dependency underneath it and authors should not have to spell it.
-/
abbrev LogicalProcessNetwork : Type (max u w v r m o) :=
  LogicalProcessNetworkCore plan.topology plan.message Obligations

/--
**No send happens on a closed or dead session.**

The theorem `sessionOpenIsRecorded` exists for, and the one
`Grass/Process/Network/Transition.lean`'s `KillsSession` docstring said was
still missing when it was written: producing `SessionStatus.died` is real
progress and does not by itself close the channel to sends.

Three fields compose. `ChannelContract.sendOnOpenSession` says a send implies
the contract's `SessionOpen` held; `sessionOpenIsRecorded` says that assertion
is the recorded status; and `SessionStatus` has exactly three constructors, so
"not open" is "closed or died".
-/
theorem no_send_on_a_closed_session {edge : plan.topology.ChannelKind}
    {message : plan.message edge}
    {occurrence : plan.topology.ChannelOccurrence edge message}
    {before after : plan.LogicalProcessNetwork}
    (sent : (plan.steps edge).Send message occurrence before after)
    (shut : (before.sessions edge occurrence.1).status ≠ .open) : False :=
  shut (plan.sessionOpenIsRecorded edge occurrence.1 before
    ((plan.channel edge).sendOnOpenSession message occurrence before after sent))

/--
**A send really puts the message in flight.**

Two fields compose. `ChannelContract.send` hands the channel
`Escrow message occurrence` as its postcondition — on an open session, which
`sendOnOpenSession` demands rather than assumes — and `escrowImpliesOutstanding`
says that claim is the ledger's. So after a send the occurrence is created and
unresolved, not merely asserted to be by a contract that chose what its own
assertion means.

An earlier version took the escrow claim as a hypothesis and had no `Send` in it
at all: it was `escrowImpliesOutstanding` eta-expanded, named as though it were
a theorem about sends, with a docstring describing a composition the statement
did not perform. Local adversarial review found it. The composition is what
makes the name true, and it is what a driver actually holds — a send it took,
not an assertion it was handed.
-/
theorem send_puts_it_in_flight {edge : plan.topology.ChannelKind}
    {carried : plan.message edge}
    {occurrence : plan.topology.ChannelOccurrence edge carried}
    {before after : plan.LogicalProcessNetwork}
    (sent : (plan.steps edge).Send carried occurrence before after)
    (sendPre : ((plan.channel edge).SendPre carried).holds before) :
    (after.inFlight edge occurrence.1).Outstanding ⟨carried, occurrence⟩ :=
  plan.escrowImpliesOutstanding edge carried occurrence after
    ((plan.channel edge).send_needs_an_open_session carried occurrence sent sendPre).2

/-- The canonical agreement this plan's contracts are stated over. -/
noncomputable abbrev agreement :
    WorldAgreement plan.topology plan.LogicalProcessNetwork :=
  logicalWorldAgreement plan.topology plan.message Obligations

/--
**The boundary projection**, from the root protocol's demands into the driver
boundary's.

Derived from `ProcessGraph.rootBoundary` rather than declared again; see the
module note on why a second object with the same job would be a defect.
`none` is the whole content of "selected": a root-local demand that projects to
`none` stays private, which is §3's "nested and flattened internal demands remain
private".
-/
def rootLocalDemandProjection :
    (plan.topology.protocol plan.topology.root).Demand → Option boundary.Demand :=
  plan.topology.rootBoundary.exportDemand

/-- A root-local demand the boundary never sees. -/
def PrivateDemand
    (demand : (plan.topology.protocol plan.topology.root).Demand) : Prop :=
  plan.rootLocalDemandProjection demand = none

/-- And one it does. -/
def ExportedDemand
    (demand : (plan.topology.protocol plan.topology.root).Demand) : Prop :=
  ∃ exported, plan.rootLocalDemandProjection demand = some exported

/--
Every root-local demand is either private or exported, and never both.

Trivial from `Option`, and stated because it is the property "selected" reduces
to: the projection is total as a *classification* even though it is partial as a
map, so no demand is unaccounted for.
-/
theorem demand_private_or_exported
    (demand : (plan.topology.protocol plan.topology.root).Demand) :
    plan.PrivateDemand demand ∨ plan.ExportedDemand demand := by
  unfold PrivateDemand ExportedDemand
  cases projected : plan.rootLocalDemandProjection demand with
  | none => exact Or.inl rfl
  | some exported => exact Or.inr ⟨exported, rfl⟩

/-! ## Well-formedness -/

/--
Everything a network under this plan must satisfy.

For now this is exactly `LogicalProcessNetworkCore.WellFormed`, and it is a
named wrapper rather than an alias because `Transition.lean` will add the
clauses a plan can state and a bare network cannot — that a step's channel
transitions are the ones this plan's contracts govern, and that the escrow
resolutions are the transition family's.

An earlier revision put the reroute-landing law here, on the argument that only
a plan holds every session's ledger. That was wrong by one layer:
`LogicalProcessNetworkCore.inFlight` already holds every ledger of every edge,
and a reroute's destination is a `ChannelId` of the same edge, so the law
belongs to the world and is `ReroutesLand` there.
-/
structure Sound (network : plan.LogicalProcessNetwork) : Prop where
  /-- Slots, lifecycles, root uniqueness, parenthood, nominals, reroutes. -/
  core : network.WellFormed

/-- A sound network's terminated instances yield their exact results. -/
theorem terminated_result_is_exact {network : plan.LogicalProcessNetwork}
    (sound : plan.Sound network) {kind slot incarnation}
    (found : network.instances kind slot = some incarnation)
    {result : (plan.topology.protocol incarnation.kind).TerminalResult}
    (ended : incarnation.lifecycle = .terminated result) :
    (plan.topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result :=
  network.terminated_result_is_exact sound.core found ended

/--
A send on any edge establishes that edge's escrow, and needs no session
hypothesis from the caller.

The plan-level statement of `docs/PROCESS.md` §3's send triple: whichever edge a
message goes out on, the contract for *that* edge governs it, there is no edge
without a contract because `channel` is total, and the open-session requirement
comes from the contract's own `sendOnOpenSession` rather than from whoever
invokes this.
-/
theorem send_establishes_escrow (edge : plan.topology.ChannelKind)
    (message : plan.message edge)
    (occurrence : plan.topology.ChannelOccurrence edge message)
    {before after : plan.LogicalProcessNetwork}
    (stepped : (plan.steps edge).Send message occurrence before after)
    (sendPre : ((plan.channel edge).SendPre message).holds before) :
    ((plan.channel edge).Escrow message occurrence).holds after :=
  ((plan.channel edge).send_needs_an_open_session message occurrence stepped
    sendPre).2

/--
And the receiver's precondition is separate from that escrow, on every edge.

`Grass/Process/Network/Channel.lean` proves it per contract; this says it holds
across the whole plan, which is what a weave argument quantifying over edges
needs.
-/
theorem receive_precondition_is_separable (edge : plan.topology.ChannelKind)
    (message : plan.message edge)
    (occurrence : plan.topology.ChannelOccurrence edge message) :
    NetworkAssertion.Separate
      ((plan.channel edge).ReceiverPre message occurrence)
      ((plan.channel edge).Escrow message occurrence) :=
  (plan.channel edge).receiverPre_separate_from_escrow message occurrence

end ProcessPlan

end Grass.Process
