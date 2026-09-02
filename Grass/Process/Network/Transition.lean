import Grass.Process.Network.Plan

/-!
# What one step of a logical process network is

`docs/PROCESS.md` §3 declares `NetworkTransition` with twenty-three constructors
and then says what the enumeration is for:

> Each constructor carries exact pre/post worlds, endpoint incarnations, the
> demand/channel embedding, occurrence and resolve token, lifecycle authority,
> and obligation equation. Routing coverage proves every endpoint input/output
> enters through exactly one constructor: no fabrication, bypass, or
> unclassified death is possible.

and, about freshness:

> `allocatedNominals` is definitionally empty for nonallocating transitions and
> contains every new process generation, channel epoch, local/child/message
> occurrence, restart identity, and coalesced replacement for allocating ones.
> Thus freshness is a fact about the exact before/after transition and every
> other step preserves history by `historyExact`; no ambient predicate can
> reinterpret it as current-live freshness.

## Every constructor names its scope

The organising idea here is not in §3's declaration but is what makes it
checkable: **each constructor carries the set of fragments it may change**, and
a proof that it changed nothing else. `TouchesOnly` below is that, stated over
`LogicalProcessNetworkCore.Agrees` — the same relation
`Grass/Process/Network/Assertion.lean`'s framing is stated over.

That is what §8's `WeaveInvariantMixin` means by `TransitionScope step`, and it
is what turns `Grass/Process/Network/Channel.lean`'s
`escrow_survives_unrelated_steps` from a theorem with a hypothesis into a
theorem about *steps*: a mixin whose assertion avoids a transition's scope is
preserved by it, and the scope is now something a transition supplies rather
than something a caller asserts.

## The ten endings share a shape and stay ten constructors

`receive`, `acknowledgeCancel`, `timedOut`, `channelClosed`, `senderDied`,
`receiverDied`, `channelDied`, `dropped`, `rerouted` and `coalesced` all do the
same thing to the world: they take one outstanding occurrence on one session and
write one `ChannelResolution` for it. `ResolvesEscrow` is that shape, and it is
shared.

They stay ten constructors rather than one `resolve` carrying a
`ChannelResolution`, because §3's routing-coverage claim is about constructors:
"every endpoint input and output enters through exactly one constructor". A
single constructor would make the claim vacuous — everything enters through the
one — and would lose the property `resolution_is_exact` proves, that a
constructor determines which resolution was written.

## What is not here

`allocatedNominals` is `Grass/Process/Nominal.lean`'s `Allocation`, and the
freshness law is `NominalHistory.Admissible` — both already existed, so
`NetworkStep` is thin. What it is *not* is a claim that this file's constructors
allocate the right nominals: each supplies its own allocation, and nothing yet
checks that a spawn's allocation contains the generation the spawned instance
carries. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.18 records that.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o}

namespace ProcessPlan

variable (plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations)

/--
A step changed nothing outside these fragments.

The scope `docs/PROCESS.md` §8 quantifies over when it says a mixin frames past
a transition whose scope is disjoint from its own. Stated over the canonical
agreement, so it composes directly with
`Grass/Process/Network/Assertion.lean`'s frame rule.
-/
def TouchesOnly (before after : plan.LogicalProcessNetwork)
    (scope : NetworkFragment plan.topology → Prop) : Prop :=
  ∀ fragment, ¬ scope fragment →
    LogicalProcessNetworkCore.Agrees fragment before after

/-- Nothing changed at all. -/
theorem touchesOnly_refl (network : plan.LogicalProcessNetwork)
    (scope : NetworkFragment plan.topology → Prop) :
    plan.TouchesOnly network network scope :=
  fun fragment _ => LogicalProcessNetworkCore.agrees_refl fragment network

/-- A smaller scope is a stronger claim. -/
theorem touchesOnly_mono {before after : plan.LogicalProcessNetwork}
    {narrow wide : NetworkFragment plan.topology → Prop}
    (contained : ∀ fragment, narrow fragment → wide fragment)
    (touched : plan.TouchesOnly before after narrow) :
    plan.TouchesOnly before after wide :=
  fun fragment outside => touched fragment (fun inNarrow => outside (contained fragment inNarrow))

/--
One occurrence on one session stops being in flight.

The shape shared by every ending in `Grass/Process/Network/Escrow.lean`'s
`ChannelResolution`. The `resolution` parameter is what distinguishes the ten
constructors that use it.
-/
structure ResolvesEscrow (before after : plan.LogicalProcessNetwork)
    (edge : plan.topology.ChannelKind) (session : plan.topology.ChannelId edge)
    (occurrence : EdgeOccurrence plan.topology plan.message edge)
    (resolution : ChannelResolution
      (EdgeOccurrence plan.topology plan.message edge)
      (plan.topology.ChannelId edge)) : Prop where
  /-- It was in flight. -/
  wasOutstanding : (before.inFlight edge session).Outstanding occurrence
  /-- It is now ended, by exactly this resolution. -/
  nowResolved : (after.inFlight edge session).resolution occurrence = some resolution
  /-- The ledger only moved forward: nothing erased, nothing reordered. -/
  ledgerExtends : LedgerExtends (before.inFlight edge session) (after.inFlight edge session)
  /-- And nothing outside this session's escrow changed. -/
  scope : plan.TouchesOnly before after (fun fragment => fragment = .escrow edge session)

namespace ResolvesEscrow

variable {plan}

/-- The resolution a step wrote is the one its constructor names. -/
theorem resolution_is_exact {before after edge session occurrence resolution}
    (resolved : plan.ResolvesEscrow before after edge session occurrence resolution)
    {other} (alsoResolved :
      (after.inFlight edge session).resolution occurrence = some other) :
    resolution = other :=
  (after.inFlight edge session).atMostOneRecordedEnding resolved.nowResolved alsoResolved

/-- An occurrence that was already ended cannot be ended again. -/
theorem cannot_resolve_twice {before after edge session occurrence resolution}
    (resolved : plan.ResolvesEscrow before after edge session occurrence resolution)
    {earlier} (alreadyEnded :
      (before.inFlight edge session).resolution occurrence = some earlier) : False := by
  rw [resolved.wasOutstanding.2] at alreadyEnded
  exact absurd alreadyEnded (by simp)

/-- Every other session's escrow is untouched, so buffered delay elsewhere is sound. -/
theorem other_sessions_untouched {before after edge session occurrence resolution}
    (resolved : plan.ResolvesEscrow before after edge session occurrence resolution)
    {otherEdge : plan.topology.ChannelKind}
    {otherSession : plan.topology.ChannelId otherEdge}
    (different : NetworkFragment.escrow otherEdge otherSession
      ≠ NetworkFragment.escrow edge session) :
    before.inFlight otherEdge otherSession = after.inFlight otherEdge otherSession :=
  resolved.scope (.escrow otherEdge otherSession) different

/-- And so is every instance, region, obligation and observation. -/
theorem observations_untouched {before after edge session occurrence resolution}
    (resolved : plan.ResolvesEscrow before after edge session occurrence resolution) :
    before.observations = after.observations :=
  resolved.scope .observations (by simp)

end ResolvesEscrow

/--
A send: one occurrence joins a session's escrow.

The counterpart of `ResolvesEscrow`, and the only transition that adds to a
ledger. `contractual` is what ties it to the plan: the step is one the edge's
own `ChannelSteps.Send` admits, so a send that no contract governs is not a
`SendsEscrow`.
-/
structure SendsEscrow (before after : plan.LogicalProcessNetwork)
    (edge : plan.topology.ChannelKind) (message : plan.message edge)
    (occurrence : plan.topology.ChannelOccurrence edge message) : Prop where
  /-- The edge's own send relation admits this step. -/
  contractual : (plan.steps edge).Send message occurrence before after
  /-- It was not escrowed before. -/
  wasFresh : ⟨message, occurrence⟩ ∉ (before.inFlight edge occurrence.1).created
  /-- It is escrowed now. -/
  nowEscrowed : (after.inFlight edge occurrence.1).Outstanding ⟨message, occurrence⟩
  /-- The ledger only moved forward. -/
  ledgerExtends :
    LedgerExtends (before.inFlight edge occurrence.1) (after.inFlight edge occurrence.1)
  /-- And nothing outside this session's escrow changed. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .escrow edge occurrence.1)

namespace SendsEscrow

variable {plan}

/-- A send establishes the edge contract's escrow assertion. -/
theorem establishes_escrow {before after edge message occurrence}
    (sent : plan.SendsEscrow before after edge message occurrence)
    (sendPre : ((plan.channel edge).SendPre message).holds before) :
    ((plan.channel edge).Escrow message occurrence).holds after :=
  ((plan.channel edge).send_needs_an_open_session message occurrence
    sent.contractual sendPre).2

/-- And it happened on an open session, which the contract demands rather than assumes. -/
theorem on_an_open_session {before after edge message occurrence}
    (sent : plan.SendsEscrow before after edge message occurrence) :
    ((plan.channel edge).SessionOpen occurrence.1).holds before :=
  (plan.channel edge).sendOnOpenSession message occurrence before after sent.contractual

end SendsEscrow

/--
One instance slot changed, and nothing else did.

The shape shared by the transitions that act on a process rather than on a
channel. Which slot, and how it changed, is the constructor's business; that it
changed nothing else is here.
-/
structure ChangesOneInstance (before after : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind) : Prop where
  /-- Nothing outside that slot changed. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .instanceState kind slot)

/--
A transition that ends one instance, storing the exact ending.

`docs/DECISIONS.md` decision 129: the ending is stored, so an audit reads it
from the network rather than replaying the parent's transition. This structure
is what writes it.
-/
structure EndsInstance (before after : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
    (ending : ProcessLifecycle (plan.topology.protocol kind)) : Prop where
  /-- It was live. -/
  wasLive : ∃ incarnation, before.instances kind slot = some incarnation ∧
    incarnation.Live
  /-- It now carries exactly this ending. -/
  nowEnded : ∃ incarnation, after.instances kind slot = some incarnation ∧
    ∃ sameKind : incarnation.kind = kind, sameKind ▸ incarnation.lifecycle = ending
  /-- Only that slot changed. -/
  onlyThatSlot : plan.ChangesOneInstance before after kind slot

namespace EndsInstance

variable {plan}

/-- An ended instance is not live afterwards, whatever the ending was. -/
theorem not_live_after {before after kind slot ending}
    (ended : plan.EndsInstance before after kind slot ending)
    (notRunning : ending ≠ .running) :
    ∃ incarnation, after.instances kind slot = some incarnation ∧ ¬ incarnation.Live := by
  obtain ⟨incarnation, found, sameKind, carries⟩ := ended.nowEnded
  refine ⟨incarnation, found, ?_⟩
  intro live
  have running := ProcessLifecycle.live_iff_running.mp live
  cases sameKind
  rw [running] at carries
  exact notRunning carries.symm

end EndsInstance

end ProcessPlan

end Grass.Process
