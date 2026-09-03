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

## The escrow resolutions share a shape, and four of them have outgrown it

`acknowledgeCancel`, `timeout`, `senderDeath`, `receiverDeath`, `drop` and
`coalesce` all do the same thing to the world: they take one outstanding
occurrence on one session and write one `ChannelResolution` for it.
`ResolvesEscrow` is that shape, and those six share it.

Four no longer do, and each moved out for a reason a consumer found.
`receive` is a `Delivers` because it advances the receiver's session cursor;
`channelClose` a `ClosesSession` and `channelDeath` a `KillsSession` because
they move the session's *status*, which nothing could produce while they were
bare resolutions; and `reroute` a `Reroutes` because it has to write the
destination's ledger, which `ResolvesEscrow`'s scope forbade.

They stay separate constructors rather than one `resolve` carrying a
`ChannelResolution`, because §3's routing-coverage claim is about constructors:
"every endpoint input and output enters through exactly one constructor". A
single constructor would make the claim vacuous — everything enters through the
one — and would lose the property `resolution_is_exact` proves, that a
constructor determines which resolution was written.

The same argument is why `childLifecycle` was split into `childCancelled` and
`childDied`: taking an arbitrary `ProcessLifecycle` it subsumed `interrupt`,
`fault`, `environmentViolation` and `processTermination`, so "exactly one
constructor" was false on the instance-ending side.

## What is not here

`allocatedNominals` is `Grass/Process/Nominal.lean`'s `Allocation`, and the
freshness law is `NominalHistory.Admissible` — both already existed, so
`NetworkStep` is thin. `Spawns.allocatesTheGeneration` and
`Restarts.allocatesTheGeneration` now do check that the allocation contains the
generation the instance carries, which closes what
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.18 recorded.

What is still not checked is the other direction: `send`, `coalesce` and
`reroute` create message occurrences and are declared non-allocating, against
§3's list of what `allocatedNominals` contains. §10.36 records it.
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

/--
The receiver consumes an occurrence and advances its own cursor.

A separate structure from `ResolvesEscrow` rather than a use of it, because its
*scope is wider*: a delivery moves the escrow ledger **and** the session cursor.

That distinction is the whole reason this exists. With `receive` built on
`ResolvesEscrow` alone, no constructor of `NetworkTransition` named `.session`
in its scope at all — so by `touchesOnly` a session's `delivered` count and its
status could never move, for any step of any program. `ChannelSession.delivered`
was provably constant, and a weave mixin about a session cursor framed past
every step in the program, vacuously. `Grass/Process/Weave/Lens.lean`'s review
is what surfaced it; the same defect for shared regions is recorded on
`StepsLocally` below.

`statusUnchanged` is what keeps the widening honest: a delivery advances the
cursor and does not close a channel, so a caller reading the status still learns
something from it.

`contractual` was missing for four review passes, and its absence was the whole
receive half of `Grass/Process/Network/Plan.lean`'s promised tie between a plan's
contracts and its transitions. `SendsEscrow` had it; `ChannelSteps.Receive` was
mentioned by no structure in this file, so `ChannelContract.receive` — §3's
`ReceiverPre * Escrow ⊢ ReceiverPost` — was spent by nothing, and a `receive`
transition could deliver an occurrence the plan's own relation forbids,
including one whose `ReceiverPre` is false. Local adversarial review found it by
grepping for the one place `plan.steps` was used and noticing there was only one.
-/
structure Delivers (before after : plan.LogicalProcessNetwork)
    (edge : plan.topology.ChannelKind) (session : plan.topology.ChannelId edge)
    (occurrence : EdgeOccurrence plan.topology plan.message edge) : Prop where
  /-- The edge's own receive relation admits this step. -/
  contractual : (plan.steps edge).Receive occurrence.1 occurrence.2 before after
  /--
  **And it is this session's occurrence.**

  `session` and `occurrence` were independent parameters, so a delivery could
  read one session's ledger and advance another's cursor. Every other field is
  stated at `session` and the occurrence carries its own, which is exactly the
  shape `Spawns.slotAgrees` was added to close for instances.
  -/
  onItsSession : occurrence.2.1 = session
  /-- It was in flight. -/
  wasOutstanding : (before.inFlight edge session).Outstanding occurrence
  /-- It is now received. -/
  nowResolved : (after.inFlight edge session).resolution occurrence = some .received
  /-- The ledger only moved forward. -/
  ledgerExtends : LedgerExtends (before.inFlight edge session) (after.inFlight edge session)
  /-- **The receiver's cursor advances by exactly one.** -/
  cursorAdvances : (after.sessions edge session).delivered =
    (before.sessions edge session).delivered + 1
  /-- And the session is not closed by being read from. -/
  statusUnchanged : (after.sessions edge session).status = (before.sessions edge session).status
  /-- This session's escrow and this session's cursor, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .escrow edge session ∨ fragment = .session edge session)

namespace Delivers

variable {plan}

/--
**A delivery establishes the receiver's postcondition.**

`docs/PROCESS.md` §3: receive "consumes `ReceiverPre * Escrow` and establishes
`ReceiverPost`; the sender never fabricates receiver state." The counterpart of
`SendsEscrow.establishes_escrow`, and the theorem `contractual` exists for: until
that field, `ChannelContract.receive` was a law about a relation no transition
invoked.
-/
theorem establishes_receiverPost {before after edge session occurrence}
    (delivered : plan.Delivers before after edge session occurrence)
    (receiverPre : ((plan.channel edge).ReceiverPre occurrence.1 occurrence.2).holds before)
    (escrowed : ((plan.channel edge).Escrow occurrence.1 occurrence.2).holds before) :
    ((plan.channel edge).ReceiverPost occurrence.1 occurrence.2).holds after :=
  (plan.channel edge).receive occurrence.1 occurrence.2 before after
    delivered.contractual receiverPre escrowed

end Delivers

/--
A channel is closed in the ordinary way.

Like `Delivers`, wider than `ResolvesEscrow` because it moves the session's
status. `docs/PROCESS.md` §3's `SessionStatus` has a `closed` constructor, and
before this nothing could ever produce one.
-/
structure ClosesSession (before after : plan.LogicalProcessNetwork)
    (edge : plan.topology.ChannelKind) (session : plan.topology.ChannelId edge)
    (occurrence : EdgeOccurrence plan.topology plan.message edge) : Prop where
  /-- It was in flight. -/
  wasOutstanding : (before.inFlight edge session).Outstanding occurrence
  /-- It is now resolved as closed. -/
  nowResolved : (after.inFlight edge session).resolution occurrence = some .channelClosed
  /-- The ledger only moved forward. -/
  ledgerExtends : LedgerExtends (before.inFlight edge session) (after.inFlight edge session)
  /-- It was open; a channel is not closed twice, and not un-died. -/
  wasOpen : (before.sessions edge session).status = .open
  /-- **And the session is closed.** -/
  nowClosed : (after.sessions edge session).status = .closed
  /-- A close delivers nothing, so the cursor does not move. -/
  cursorUnchanged : (after.sessions edge session).delivered =
    (before.sessions edge session).delivered
  /-- This session's escrow and this session's cursor, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .escrow edge session ∨ fragment = .session edge session)

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

Once shared by every transition acting on a process; now `Detaches` alone uses
it. `EndsInstance` outgrew it when the obligation ledger became reachable, and
`Joins` when a live incarnation turned out to be able to vanish through it
unclassified.
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
    (ending : ProcessLifecycle (plan.topology.protocol kind))
    (custody : Bag (plan.topology.protocol kind).Demand →
      Obligations → Obligations → Prop) : Prop where
  /--
  **The ending really ends it.**

  Without this `EndsInstance` accepted `ending := .running`, so a step could move
  the obligation ledger while the process it "ended" was still stepping — and
  `moving_the_ledger_ends_an_instance` reported that as an ending. Local
  adversarial review built one at a plan with two obligation values.

  `not_live_after` was guarded by the same condition as a hypothesis, which is
  the tell: the guard belonged in the structure.
  -/
  notRunning : ending ≠ .running
  /-- It was live. -/
  wasLive : ∃ incarnation, before.instances kind slot = some incarnation ∧
    incarnation.Live
  /-- It now carries exactly this ending. -/
  nowEnded : ∃ incarnation, after.instances kind slot = some incarnation ∧
    ∃ sameKind : incarnation.kind = kind, sameKind ▸ incarnation.lifecycle = ending
  /--
  **And it is the same incarnation, ended.**

  `nowEnded` constrains the lifecycle and nothing else, so an ending could swap
  the incarnation's generation, re-parent it, or change the request it was
  started with — the same hole `StepsLocally.protocolStep` had, with the same
  consequence: a non-allocating step installing a generation nothing allocated,
  against `docs/FOUNDATION.md` law 22.

  `outstanding` is deliberately left free: disposing of it is what an ending
  *does*, and §2's three-way partition of it is
  `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.33.
  -/
  identityPreserved : ∃ (fromInstance toInstance : ProcessInstance plan.topology)
      (fromKind : fromInstance.kind = kind) (toKind : toInstance.kind = kind),
    before.instances kind slot = some fromInstance ∧
    after.instances kind slot = some toInstance ∧
    toKind ▸ toInstance.ref = fromKind ▸ fromInstance.ref ∧
    toKind ▸ toInstance.parentage = fromKind ▸ fromInstance.parentage ∧
    toKind ▸ toInstance.request = fromKind ▸ fromInstance.request ∧
    toKind ▸ toInstance.localState = fromKind ▸ fromInstance.localState
  /--
  **And the obligation ledger moves exactly as this ending declared.**

  `docs/PROCESS.md` §2: "termination explicitly resolves, transfers, or permits
  pending". `custody` is a parameter rather than a field, so it is the
  *constructor* that names the transfer and a reader of the transition sees it —
  the same trade as `emitted` on `Commits`.

  **Indexed by the bag being disposed of.** An earlier version took only the two
  ledgers, so the transfer said nothing about *what* was being transferred and
  §2's "pending" had no referent at the network: three outstanding demands could
  vanish at a termination with nothing accounting for them. It still does not
  carry §2's three-way *partition* — that wants the specification's
  `TerminalRemainderLaw`, which a `ProcessPlan` does not hold; see
  `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.33.

  Before this existed, no constructor of `NetworkTransition` named
  `.obligations` in its scope, so by `touchesOnly` the ledger
  `Grass/Process/Network/World.lean` deliberately parameterises could never move
  in any program at all. A weave mixin about obligations framed past every step
  vacuously, and §7's `DisjointOrCommutingObligations` was satisfied by the
  whole family for free.

  The second conjunct of `custodyDeclared` is what stops
  `custody := fun _ _ _ => True`: requiring the declared relation to be
  single-valued at the before-state turns it from a claim the author can make
  vacuously into one that pins the outcome, which is the same move
  `Grass/Process/Function/Serial.lean` makes with
  `SerialFunctionRealizes.converse`. At any plan whose `Obligations` has two
  values, `True` is refuted.
  -/
  custodyDeclared : ∃ incarnation, before.instances kind slot = some incarnation ∧
    ∃ sameKind : incarnation.kind = kind,
      custody (sameKind ▸ incarnation.outstanding) before.obligations after.obligations ∧
      ∀ other, custody (sameKind ▸ incarnation.outstanding) before.obligations other →
        other = after.obligations
  /--
  That slot, and the ledger if the ledger moved.

  The guard is the *actual* change rather than a flag the author sets, which is
  what keeps the scope exact: a step that transferred nothing does not declare
  the ledger, so a mixin about obligations frames past it, correctly. The
  observation-trace scope above learned this the hard way — a scope that is too
  wide is invisible to every test the producing module can write and defeats
  every scheduling argument downstream.
  -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .instanceState kind slot ∨
      (before.obligations ≠ after.obligations ∧ fragment = .obligations))

namespace EndsInstance

variable {plan}

/-- An ended instance is not live afterwards, whatever the ending was. -/
theorem not_live_after {before after kind slot ending custody}
    (ended : plan.EndsInstance before after kind slot ending custody) :
    ∃ incarnation, after.instances kind slot = some incarnation ∧ ¬ incarnation.Live := by
  obtain ⟨incarnation, found, sameKind, carries⟩ := ended.nowEnded
  refine ⟨incarnation, found, ?_⟩
  intro live
  have running := ProcessLifecycle.live_iff_running.mp live
  cases sameKind
  rw [running] at carries
  exact ended.notRunning carries.symm

end EndsInstance


/--
How one instance's outstanding demand bag moves across one event.

`docs/PROCESS.md` §2's run relation, at the network. `ProcessEvent.settles`
splits the five events into the two that answer an outstanding demand and the
three that do not, and this is the same split: an answering event removes
exactly one `cons` before the issued bag is added, and a non-answering one adds
without removing.

Stated once here rather than inline in `StepsLocally`, because it is the same
equation `Grass/Process/Run.lean` proves the four linearity clauses about — no
fabrication, no replay, no joint consumption, no silent loss — and a second
spelling would be a second thing to keep in step.
-/
def SettlesDemands {kind : plan.topology.ProcessKind}
    (event : (plan.topology.protocol kind).Event)
    (issued before after : Bag (plan.topology.protocol kind).Demand) : Prop :=
  match event.settles with
  | none => after = before + issued
  | some demand => ∃ remainder,
      Bag.ConsumeExactlyOneMatching before demand remainder ∧ after = remainder + issued

/--
One instance takes a protocol step.

Its private state moves by the protocol's own `Step` relation, observations may
be appended, and it may write the shared regions its role has write access to —
which is why the scope is three families of fragment rather than one.

Two earlier drafts got this wrong in the same direction. The first scoped it to
the instance slot alone, which is false of any step that emits. The second added
observations and stopped, which is false of any step that writes shared state —
and that one was invisible until `Grass/Process/Weave/Mixin.lean` tried to state
an invariant about a shared region and found that *no constructor in this family
could touch one*. A weave mixin about shared state would have framed past every
step in the program, vacuously and wrongly.

`writesPermitted` is what keeps the widening honest: a step may only name
regions its own role may write, so `ProcessGraph.sharedAccess` still decides who
touches what.
-/
structure StepsLocally (before after : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
    (event : (plan.topology.protocol kind).Event)
    (emitted : Trace boundary.Observation)
    (issued : Bag (plan.topology.protocol kind).Demand)
    (localEmitted : ObservationSegment (plan.topology.protocol kind).Observation) :
    Prop where
  /-- It was live, and this is the state it stepped from. -/
  from' : ∃ incarnation, before.instances kind slot = some incarnation ∧
    incarnation.Live ∧ incarnation.kind = kind
  /-- It is still live afterwards; a step that ends a process is a different
  constructor. -/
  stillLive : ∃ incarnation, after.instances kind slot = some incarnation ∧
    incarnation.Live
  /--
  **And its private state moves by the protocol's own `Step` relation.**

  The field this structure spent four revisions without, while its docstring
  claimed it. `event` was a parameter used nowhere, `issued` did not exist, and
  the instance's new state was arbitrary as long as it was live — so a
  `processStep` was not a protocol step at all, and no fixture in the corpus ever
  constructed one to notice.

  With it, five things §3 requires of a local step are here: the protocol admits
  the transition, the demands it issues are the protocol's own, the observation
  segment is the one the protocol emitted, the issued bag reaches the instance's
  outstanding demands by §2's linear equation (`SettlesDemands`) rather than
  being discarded, and **the incarnation stays the same incarnation**.

  The last clause was the second thing missing here. `ProcessInstance` has seven
  fields and this constrained two, so one tick could move an instance to a
  different generation and re-parent it under another role — installing a
  generation nothing allocated, which is `docs/FOUNDATION.md` law 22, while
  `allocatedNominals` said the step allocated nothing. Local adversarial review
  built exactly that step and proved the network after it fails
  `NominalsAllocated` and `ParentageValid`.
  -/
  protocolStep : ∃ (fromInstance toInstance : ProcessInstance plan.topology)
      (fromKind : fromInstance.kind = kind) (toKind : toInstance.kind = kind),
    before.instances kind slot = some fromInstance ∧
    after.instances kind slot = some toInstance ∧
    (plan.topology.protocol kind).Step (fromKind ▸ fromInstance.localState) event
      (toKind ▸ toInstance.localState) issued localEmitted ∧
    plan.SettlesDemands event issued (fromKind ▸ fromInstance.outstanding)
      (toKind ▸ toInstance.outstanding) ∧
    toKind ▸ toInstance.ref = fromKind ▸ fromInstance.ref ∧
    toKind ▸ toInstance.parentage = fromKind ▸ fromInstance.parentage ∧
    toKind ▸ toInstance.request = fromKind ▸ fromInstance.request
  /--
  **And what reaches the network trace is the projection of what it observed.**

  `ProcessGraph.observeAt` is the declaration; this is where it is spent. Before
  it, `emitted` was an arbitrary boundary segment: a step could append anything
  to the program's trace regardless of what the role observed.
  -/
  emittedIsProjected : emitted = localEmitted.filterMap (plan.topology.observeAt kind)
  /--
  **What it produced joins the pending trace, and the committed trace does not
  move.**

  `docs/PROCESS.md` §6: "step emissions name only portable logical observations",
  and "a driver commit is the sole transition allowed to … append a committed
  external observation". A step produces; only `Commits` publishes. Until
  `NetworkFragment.pending` existed both appended to one trace, which left
  `Commits` with nothing to be about — see that structure.
  -/
  producesPending : after.pending = before.pending ++ emitted
  /--
  **And every region it actually changed is one its role may write.**

  `docs/PROCESS.md` §3: shared logical state is "named separately with
  read/write/atomic capabilities", and this is where that capability is spent
  rather than merely declared.

  Quantified over the regions that *moved* rather than over a `written`
  predicate the author supplied. The declared form was the same widening the
  observation scope had: a step could name a region it may write and did not
  write, and `Grass/Process/Trace/Independence.lean` reads independence off
  exactly these predicates, so two steps touching nothing in common would fail
  to commute because one of them said it might.
  -/
  writesPermitted : ∀ region, before.shared region ≠ after.shared region →
    (plan.topology.sharedAccess kind region).mayWrite = true
  /--
  Its slot, the regions it wrote, the observation trace **if it actually
  emitted**, and nothing else.

  The `emitted ≠ []` guard is the third correction to this scope and the one a
  consumer found. Declaring `.observations` unconditionally is *sound* — the
  step really does touch nothing else — but it makes every process step
  non-independent of every other, because
  `Grass/Process/Trace/Independence.lean` reads independence off exactly these
  predicates. Two steps on unrelated instances that emit nothing would then
  never commute, and `docs/PROCESS.md` §7's Mazurkiewicz congruence would be the
  identity.

  A scope that is too *wide* costs nothing the producing module can see and
  everything a scheduling argument needs, which is the mirror of the too-narrow
  failure recorded above.
  -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .instanceState kind slot ∨
      (emitted ≠ [] ∧ fragment = .pending) ∨
      ∃ region, before.shared region ≠ after.shared region ∧ fragment = .region region)

/--
A new incarnation appears in a slot that was empty.

`allocation` is what `docs/PROCESS.md` §3 calls the transition's
`allocatedNominals`, and `allocatesTheGeneration` is the correspondence §10.18
records as missing everywhere else: the identity the spawned instance carries is
one this step allocated, so the history cannot omit it.
-/
structure Spawns (before after : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
    (allocation : Allocation plan.topology.Carrier)
    (emitted : Trace boundary.Observation)
    (localEmitted : ObservationSegment (plan.topology.protocol kind).Observation) :
    Prop where
  /-- The slot was empty. -/
  wasEmpty : before.instances kind slot = none
  /-- It now holds a live incarnation of the right kind. -/
  nowLive : ∃ incarnation, after.instances kind slot = some incarnation ∧
    incarnation.Live ∧ incarnation.kind = kind
  /-- Whose parent the topology permits. -/
  authorized : ∀ incarnation, after.instances kind slot = some incarnation →
    ∀ parentKind parent, incarnation.parentage.knownParent = some ⟨parentKind, parent⟩ →
      plan.topology.maySpawn parentKind incarnation.kind
  /-- And whose generation this step allocated. -/
  allocatesTheGeneration : ∀ incarnation, after.instances kind slot = some incarnation →
    incarnation.ref.generation ∈ allocation.entries
  /--
  **And it is stored where its own reference says it is.**

  `ProcessRef` has an `instanceId` as well as a generation, and
  `allocatesTheGeneration` constrains only the second — so a spawn could install
  an incarnation naming slot 3 into slot 7 and take a well-formed network to one
  failing `WellFormed.SlotsAgree`. Local adversarial review built exactly that
  step, with the before-network well formed and the after-network not.
  -/
  slotAgrees : ∀ incarnation, after.instances kind slot = some incarnation →
    ∃ sameKind : incarnation.kind = kind, sameKind ▸ incarnation.ref.instanceId = slot
  /--
  **And it starts where its own protocol says a start is.**

  The field that was missing, and the hole it left was the one `SettlesDemands`
  closes at every *step*: with no tie to `ProcessSpec.Initial`, an instance could
  be spawned already holding demands it never issued, and answer them later
  perfectly legally. Local adversarial review spawned one holding three.

  All four of `Initial`'s arguments at once, for the same reason `Initial`
  relates all four: a spawn that placed a permitted state while inventing the
  request or the outstanding bag would satisfy a weaker clause and be wrong.
  -/
  startsInitial : ∀ incarnation, after.instances kind slot = some incarnation →
    ∃ sameKind : incarnation.kind = kind,
      (plan.topology.protocol kind).Initial (sameKind ▸ incarnation.request)
        (sameKind ▸ incarnation.localState) (sameKind ▸ incarnation.outstanding) localEmitted
  /-- And what reaches the network trace is the projection of what it observed. -/
  emittedIsProjected : emitted = localEmitted.filterMap (plan.topology.observeAt kind)
  /-- What it produced joins the pending trace; see `StepsLocally`. -/
  producesPending : after.pending = before.pending ++ emitted
  /-- That slot, the nominal history, the pending trace if it produced, and
  nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .instanceState kind slot ∨ fragment = .nominals ∨
      (emitted ≠ [] ∧ fragment = .pending))

/--
A supervisor restarts a slot whose incarnation ended.

Distinct from `Spawns`, which demands the slot was *empty*. Until this existed
`restart` was a `Spawns` under a second name — the two constructors were
definitionally interchangeable — and since `EndsInstance` leaves the ended
incarnation in its slot, no restart could ever follow a death. The supervision
path `docs/PROCESS.md` §3 describes did not exist.

`wasEnded` is what distinguishes it, and it is also what makes `restart` a
different fact about the world than `spawn`: an audit reading the transition
learns that a previous incarnation ended here.
-/
structure Restarts (before after : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
    (allocation : Allocation plan.topology.Carrier)
    (emitted : Trace boundary.Observation)
    (localEmitted : ObservationSegment (plan.topology.protocol kind).Observation) :
    Prop where
  /-- **The slot held an incarnation that had ended.** -/
  wasEnded : ∃ incarnation, before.instances kind slot = some incarnation ∧
    ¬ incarnation.Live
  /-- It now holds a live incarnation of the right kind. -/
  nowLive : ∃ incarnation, after.instances kind slot = some incarnation ∧
    incarnation.Live ∧ incarnation.kind = kind
  /--
  **Whose parent the topology permits.**

  `Spawns` has had this since it was written; `Restarts` did not, so a restart
  could install a role claiming a parent the graph forbids. Local adversarial
  review built one and proved the network after it fails `ParentageValid`.
  -/
  authorized : ∀ incarnation, after.instances kind slot = some incarnation →
    ∀ parentKind parent, incarnation.parentage.knownParent = some ⟨parentKind, parent⟩ →
      plan.topology.maySpawn parentKind incarnation.kind
  /-- Whose generation this step allocated — a restart is a new incarnation. -/
  allocatesTheGeneration : ∀ incarnation, after.instances kind slot = some incarnation →
    incarnation.ref.generation ∈ allocation.entries
  /--
  **And it is stored where its own reference says it is.**

  `ProcessRef` has an `instanceId` as well as a generation, and
  `allocatesTheGeneration` constrains only the second — so a spawn could install
  an incarnation naming slot 3 into slot 7 and take a well-formed network to one
  failing `WellFormed.SlotsAgree`. Local adversarial review built exactly that
  step, with the before-network well formed and the after-network not.
  -/
  slotAgrees : ∀ incarnation, after.instances kind slot = some incarnation →
    ∃ sameKind : incarnation.kind = kind, sameKind ▸ incarnation.ref.instanceId = slot
  /--
  **And it starts where its own protocol says a start is.**

  The field that was missing, and the hole it left was the one `SettlesDemands`
  closes at every *step*: with no tie to `ProcessSpec.Initial`, an instance could
  be spawned already holding demands it never issued, and answer them later
  perfectly legally. Local adversarial review spawned one holding three.

  All four of `Initial`'s arguments at once, for the same reason `Initial`
  relates all four: a spawn that placed a permitted state while inventing the
  request or the outstanding bag would satisfy a weaker clause and be wrong.
  -/
  startsInitial : ∀ incarnation, after.instances kind slot = some incarnation →
    ∃ sameKind : incarnation.kind = kind,
      (plan.topology.protocol kind).Initial (sameKind ▸ incarnation.request)
        (sameKind ▸ incarnation.localState) (sameKind ▸ incarnation.outstanding) localEmitted
  /-- And what reaches the network trace is the projection of what it observed. -/
  emittedIsProjected : emitted = localEmitted.filterMap (plan.topology.observeAt kind)
  /-- What it produced joins the pending trace; see `StepsLocally`. -/
  producesPending : after.pending = before.pending ++ emitted
  /-- That slot, the nominal history, the pending trace if it produced, and
  nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .instanceState kind slot ∨ fragment = .nominals ∨
      (emitted ≠ [] ∧ fragment = .pending))

/--
A parent collects a terminated child and frees its slot.

`ChangesOneInstance` used to be the whole of `join`, and `ChangesOneInstance`
has exactly one field: the scope. So `join kind slot` was definitionally "any
two worlds differing in one slot" — a live incarnation could vanish with no
stored ending, no custody transfer and no lifecycle, which is the unclassified
death `docs/PROCESS.md` §3 says is impossible and the exact obligation
`docs/DECISIONS.md` decision 129 exists to enforce. Local adversarial review
built one at the M2 fixture plan.

`wasTerminated` is the fix: only a child that reached a terminal state of its
protocol may be joined, and the result it reached is the constructor's argument.
-/
structure Joins (before after : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
    (result : (plan.topology.protocol kind).TerminalResult) : Prop where
  /-- **The child had terminated, with exactly this result.** -/
  wasTerminated : ∃ incarnation, before.instances kind slot = some incarnation ∧
    ∃ sameKind : incarnation.kind = kind,
      sameKind ▸ incarnation.lifecycle = ProcessLifecycle.terminated result
  /--
  **And it was somebody's child.**

  The docstring said "a parent collects a terminated child" and nothing required
  a parent: local adversarial review joined the *root*, which is a program
  exiting by being collected by nobody. `Detaches` has carried `wasAttached`
  since it was written; this is the same field.
  -/
  wasChild : ∀ incarnation, before.instances kind slot = some incarnation →
    ¬ incarnation.IsRoot
  /-- And the slot is now free, so a restart may take it. -/
  nowFree : after.instances kind slot = none
  /-- That slot, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .instanceState kind slot)

/--
An occurrence is rerouted to another session, and arrives there.

`ResolvesEscrow`'s scope is the *source* session's escrow alone, so a `reroute`
built on it could write `rerouted destination` into one ledger and was forbidden
from touching the destination's. `WellFormed.ReroutesLand` then degenerated: it
could only hold at a destination that was already non-empty before the step, and
the reroute itself could never make one so. A reroute was a drop with a
forwarding address.

`arrives` is stated with exactly the predicate `ReroutesLand` uses, so
discharging it discharges the well-formedness clause rather than something
adjacent to it. Its weakness — that "an arrival exists" does not say the arrival
*carries this payload* — is `Grass/Process/Network/Escrow.lean`'s and is
recorded there.
-/
structure Reroutes (before after : plan.LogicalProcessNetwork)
    (edge : plan.topology.ChannelKind) (session : plan.topology.ChannelId edge)
    (occurrence : EdgeOccurrence plan.topology plan.message edge)
    (destination : plan.topology.ChannelId edge) : Prop where
  /-- It was in flight here. -/
  wasOutstanding : (before.inFlight edge session).Outstanding occurrence
  /-- It is now resolved as rerouted, to exactly this destination. -/
  nowResolved : (after.inFlight edge session).resolution occurrence =
    some (.rerouted destination)
  /-- This ledger only moved forward. -/
  ledgerExtends : LedgerExtends (before.inFlight edge session) (after.inFlight edge session)
  /-- A reroute goes somewhere else. -/
  elsewhere : destination ≠ session
  /-- **And the payload arrives at the destination.** -/
  arrives : ∃ arrival, arrival ∈ (after.inFlight edge destination).created
  /-- Whose ledger also only moved forward. -/
  destinationExtends :
    LedgerExtends (before.inFlight edge destination) (after.inFlight edge destination)
  /-- Both sessions' escrow, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .escrow edge session ∨ fragment = .escrow edge destination)

/--
A channel dies, taking its session with it.

The sibling of `ClosesSession`, and it was missing for the same reason: with
`channelDeath` built on `ResolvesEscrow` alone, `SessionStatus.died` was
producible by nothing, and a channel that had died kept whatever status it had.

Producing `.died` is not by itself a closure of the channel to further sends:
`ChannelContract.SessionOpen` is an assertion whose footprint is bounded to the
session fragment, and nothing ties its `holds` to `sessions.status`. That tie is
`Channel.lean`'s to make, and until it does, a dead session and an open one are
distinguishable by this field and not by that contract.
-/
structure KillsSession (before after : plan.LogicalProcessNetwork)
    (edge : plan.topology.ChannelKind) (session : plan.topology.ChannelId edge)
    (occurrence : EdgeOccurrence plan.topology plan.message edge) : Prop where
  /-- It was in flight. -/
  wasOutstanding : (before.inFlight edge session).Outstanding occurrence
  /-- It is now resolved by the channel's death. -/
  nowResolved : (after.inFlight edge session).resolution occurrence = some .channelDied
  /-- The ledger only moved forward. -/
  ledgerExtends : LedgerExtends (before.inFlight edge session) (after.inFlight edge session)
  /-- It was open; a dead channel is not re-killed, and a closed one not un-closed. -/
  wasOpen : (before.sessions edge session).status = .open
  /-- **And the session is dead.** -/
  nowDied : (after.sessions edge session).status = .died
  /-- A death delivers nothing, so the cursor does not move. -/
  cursorUnchanged : (after.sessions edge session).delivered =
    (before.sessions edge session).delivered
  /-- This session's escrow and this session's cursor, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .escrow edge session ∨ fragment = .session edge session)

/--
A cancellation is requested against an in-flight occurrence.

It does *not* resolve the escrow, which is the whole point:
`docs/PROCESS.md` §3 says "requesting cancellation does not reclaim escrow", and
`stillOutstanding` is that stated as a field rather than left to the reader.
-/
structure RequestsCancel (before after : plan.LogicalProcessNetwork)
    (edge : plan.topology.ChannelKind) (session : plan.topology.ChannelId edge)
    (occurrence : EdgeOccurrence plan.topology plan.message edge) : Prop where
  /-- It was in flight. -/
  wasOutstanding : (before.inFlight edge session).Outstanding occurrence
  /--
  **And no cancellation had been requested against it yet.**

  Without this every field held with `after = before` at any network where a
  cancellation was already recorded — reachable by one prior `requestCancel` —
  so `requestCancel` was a step that changed nothing. That is the `commit []`
  defect one constructor over, and it has the same consequence: a one-step
  silent cycle forces every `NetworkProgressMeasure` to declare that network at
  a frontier. Local adversarial review built it.

  Requesting a cancellation twice is not a second transition; `docs/PROCESS.md`
  §3's summary is that a request is recorded, and it is recorded once.
  -/
  wasNotRequested : (before.inFlight edge session).cancelRequested occurrence = false
  /-- The request is recorded. -/
  nowRequested : (after.inFlight edge session).cancelRequested occurrence = true
  /-- **And it is still in flight.** -/
  stillOutstanding : (after.inFlight edge session).Outstanding occurrence
  /--
  **And the ledger only moved forward.**

  Every other constructor that touches an escrow ledger carries this —
  `SendsEscrow`, `ResolvesEscrow`, `Delivers`, `ClosesSession`, `KillsSession`,
  `Reroutes` all do — and this one did not, while its scope licensed it to
  rewrite the whole session's ledger.

  Local adversarial review built the step: two occurrences in flight, the
  "request" records the cancellation on the first and *deletes the second from
  `created`*. An in-flight message destroyed with no `ChannelResolution`
  recorded, which is the unclassified death §3 forbids, evading
  `resolution_is_exact` and `cannot_resolve_twice` because no resolution was
  ever written. The same gap also permitted un-requesting another occurrence's
  cancellation, against `LedgerExtends.cancelRequestMonotone`, whose own
  docstring calls that law 7.
  -/
  ledgerExtends : LedgerExtends (before.inFlight edge session) (after.inFlight edge session)
  /-- That session's escrow, and nothing else. -/
  scope : plan.TouchesOnly before after (fun fragment => fragment = .escrow edge session)

/--
A commit appends to the observation trace, and may only append what a live
process could have produced.

`docs/PROCESS.md` §6's transition, at the only fragment it touches. Appending
rather than replacing is the content: a trace that could be rewritten would let
a reconciler drop an observation a specification demanded.

`earned` is the second half, and it was missing for five review passes.
`Commits` constrained the trace and nothing else, so nothing tied `emitted` to
anything a process observed — and a commit of an arbitrary observation was a
legal step of **every** network of every plan with an inhabited
`boundary.Observation`. Local adversarial review proved it generically
(`commits_anywhere`) and drew the consequence: since `.commit` is not
`DrivenByEntropy`, `NetworkProgressMeasure.frontierIsExternal` then forbids
*any* network from being at a frontier, §7's "remain at a declared external
frontier" escape is unreachable, and every theorem in
`Grass/Process/Network/Progress.lean` is vacuous.

The tie is the one `StepsLocally` already uses: the emitted trace is the
boundary projection of a local segment, at a role with a live incarnation. That
is weaker than "these observations were produced by that step" — which needs a
pending-observation buffer in the world, recorded as
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.58 — and it is enough to stop a commit
being enabled everywhere: a network with no live instance of a role whose
protocol can project these observations cannot take one.
-/
structure Commits (before after : plan.LogicalProcessNetwork)
    (emitted : Trace boundary.Observation) : Prop where
  /--
  **What is committed is the front of what processes produced, and it stops
  being pending.**

  The provenance field, and the whole reason `NetworkFragment.pending` exists. A
  commit can publish only what some step actually emitted, in the order it was
  emitted, and can publish it once.
  -/
  earned : before.pending = emitted ++ after.pending
  /-- The committed trace grew by exactly that much. -/
  appended : after.observations = before.observations ++ emitted
  /--
  **And it grew.**

  `docs/PROCESS.md` §6 says a commit "appends to the observation trace";
  appending nothing is not a commit. Without this field `commit []` is a
  transition whose scope is empty and which changes nothing at all — a genuine
  no-op step, at every network, in every plan.

  That is worse than untidy. It is a one-step silent cycle, so
  `Grass/Process/Network/Progress.lean`'s `no_silent_cycle` would force every
  `NetworkProgressMeasure` to declare *every* network at a frontier, and §7's
  progress theorem would be vacuous everywhere. It is also the one thing
  `Grass/Process/Trace/Independence.lean`'s `self_independent_iff_scopeless`
  calls out as degenerate: a step independent of itself.

  Found by trying to build a progress measure at the M2 fixture plan and
  discovering the measure could not exist. Trying again found that `nonempty`
  alone does not save it — see `earned` — which is the second finding this field
  produced.
  -/
  nonempty : emitted ≠ []
  /-- The two traces **if it actually appended**, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => emitted ≠ [] ∧ (fragment = .observations ∨ fragment = .pending))

/--
A parent lets a child go.

`docs/DECISIONS.md` decision 130's detach, at the network: the parentage moves
from `attached` to `detached` with the same reference, so authority is gone and
the history is not.
-/
structure Detaches (before after : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind) : Prop where
  /-- It had a parent with authority. -/
  wasAttached : ∃ incarnation, before.instances kind slot = some incarnation ∧
    incarnation.parentage.currentParent ≠ none
  /--
  **And afterwards it is exactly the detachment of what it was, and nothing else
  about it moved.**

  A detach removes authority; it is not a place to change generation, request,
  private state, *which parent is remembered*, or *whether the process is still
  alive*.

  Three earlier versions of this were wrong and each was found the same way, by
  building the attack rather than by reading. The first let generation, request
  and state move. The second pinned those and stated the parentage as a separate
  `nowDetached` field — "some detached incarnation with some remembered parent" —
  which is satisfied by a *different* detachment than the one `wasAttached`
  found: local adversarial review built a step that reparented a child onto a
  fabricated ancestor, taking a `ParentageValid` network to one that is not, and
  making `Grass/Process/Network/Child.lean`'s `NonReturningReason.detached`
  checkable against a forged history. The third omitted `lifecycle` from the
  seven `ProcessInstance` fields, and the same attack ended a live incarnation
  with no `EndsInstance`, no custody partition and no stored classification — the
  unclassified death §3 forbids, in the constructor next to the one
  `Joins.wasTerminated` was added to protect.

  Stating it as `parentage.detach` rather than as a predicate is what closes all
  three at once: `Grass/Process/Network/Instance.lean` already defines the
  transition §3 describes — "changes only `.attached parent` to `.detached
  parent`, proves the references identical" — and it was used by nothing.
  -/
  identityPreserved : ∃ (fromInstance toInstance : ProcessInstance plan.topology)
      (fromKind : fromInstance.kind = kind) (toKind : toInstance.kind = kind),
    before.instances kind slot = some fromInstance ∧
    after.instances kind slot = some toInstance ∧
    toKind ▸ toInstance.parentage = (fromKind ▸ fromInstance.parentage).detach ∧
    toKind ▸ toInstance.lifecycle = fromKind ▸ fromInstance.lifecycle ∧
    toKind ▸ toInstance.ref = fromKind ▸ fromInstance.ref ∧
    toKind ▸ toInstance.request = fromKind ▸ fromInstance.request ∧
    toKind ▸ toInstance.localState = fromKind ▸ fromInstance.localState ∧
    toKind ▸ toInstance.outstanding = fromKind ▸ fromInstance.outstanding
  /-- That slot, and nothing else. -/
  onlyThatSlot : plan.ChangesOneInstance before after kind slot

namespace Detaches

variable {plan}

/--
**It really is detached afterwards.**

Was a field; is now a consequence, because `wasAttached` says the parentage had
authority and `identityPreserved` says the new one is that parentage's `detach`.

Worth the change rather than the redundancy. The old field's second conjunct,
`knownParent ≠ none`, was implied by its first — `IsDetached` means
`.detached _ _`, whose `knownParent` is `some` by definition — so the structure
paid for a projection of a redundancy and did not buy the claim a reader takes
from "remembers which". That claim is the next theorem.
-/
theorem is_detached_afterwards {before after kind slot}
    (detached : plan.Detaches before after kind slot) :
    ∃ (incarnation : ProcessInstance plan.topology) (isKind : incarnation.kind = kind),
      after.instances kind slot = some incarnation ∧
        (isKind ▸ incarnation.parentage : ProcessParentage plan.topology kind).IsDetached := by
  obtain ⟨was, foundWas, hadAuthority⟩ := detached.wasAttached
  obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
    isDetach, _⟩ := detached.identityPreserved
  refine ⟨toInstance, toKind, foundAfter, ?_⟩
  rw [isDetach]
  refine ProcessParentage.detach_isDetached ?_
  have same : was = fromInstance := Option.some.inj (foundWas ▸ foundBefore)
  subst same
  cases fromKind
  exact hadAuthority

/--
**And it is still whatever it was — running, if it was running.**

`identityPreserved`'s `lifecycle` component, in the form a consumer wants. A
detach removes authority and is not an ending; the two are separate constructors
because §3 requires an ending to carry a custody partition and a stored
classification, and this one carries neither.

Local adversarial review built the step this refutes: a "detach" that leaves the
child `.died .parentDied`. Every field of the structure held, because `lifecycle`
was one of the three `ProcessInstance` fields `identityPreserved` did not
mention. `Tests/Process/DetachFixtures.lean`'s `a_detach_may_not_kill` is the
attack, kept.
-/
theorem the_child_survives {before after kind slot}
    (detached : plan.Detaches before after kind slot) :
    ∃ (fromInstance toInstance : ProcessInstance plan.topology),
      before.instances kind slot = some fromInstance ∧
        after.instances kind slot = some toInstance ∧
        (toInstance.Live ↔ fromInstance.Live) := by
  obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
    _, sameLifecycle, _⟩ := detached.identityPreserved
  refine ⟨fromInstance, toInstance, foundBefore, foundAfter, ?_⟩
  show toInstance.lifecycle.Live ↔ fromInstance.lifecycle.Live
  rw [← ProcessLifecycle.live_cast toKind toInstance.lifecycle,
    ← ProcessLifecycle.live_cast fromKind fromInstance.lifecycle, sameLifecycle]

/--
**And the parent it remembers is the one it was attached to.**

`docs/PROCESS.md` §3: the detach "proves the references identical". The old
field said only that *some* reference was recorded, and local adversarial review
built the step that records a different one — a forged ancestor, against which
`Grass/Process/Network/Child.lean`'s `NonReturningReason.detached` would then
check out.
-/
theorem former_parent_is_the_one_it_had {before after kind slot}
    (detached : plan.Detaches before after kind slot) :
    ∃ (fromInstance toInstance : ProcessInstance plan.topology),
      before.instances kind slot = some fromInstance ∧
        after.instances kind slot = some toInstance ∧
        toInstance.parentage.knownParent = fromInstance.parentage.knownParent := by
  obtain ⟨fromInstance, toInstance, fromKind, toKind, foundBefore, foundAfter,
    isDetach, _⟩ := detached.identityPreserved
  refine ⟨fromInstance, toInstance, foundBefore, foundAfter, ?_⟩
  rw [← ProcessParentage.knownParent_cast toKind toInstance.parentage,
    ← ProcessParentage.knownParent_cast fromKind fromInstance.parentage, isDetach,
    ProcessParentage.detach_preserves_knownParent]

end Detaches

/--
**One step of a logical process network.**

`docs/PROCESS.md` §3's constructors, twenty-four after `childLifecycle` was
split. Six of them are competing escrow resolutions sharing `ResolvesEscrow`,
distinguished by the resolution each writes; four more resolve escrow *and*
something else, and have their own structures for it; the rest carry the shape
their own effect needs. See the module note.

Every constructor determines a scope, and `touchesOnly` below proves each one
respects it. That is what §3's routing coverage means here: there is no
transition without a scope, so there is no way for a step to change a fragment
it did not declare, and §8's framing quantifies over the family rather than over
a hypothesis a caller supplies.
-/
inductive NetworkTransition (before after : plan.LogicalProcessNetwork) : Type (max u w v r m o)
  /-- One instance takes a protocol step. -/
  | processStep (kind : plan.topology.ProcessKind)
      (slot : plan.topology.InstanceId kind)
      (event : (plan.topology.protocol kind).Event)
      (emitted : Trace boundary.Observation)
      (issued : Bag (plan.topology.protocol kind).Demand)
      (localEmitted : ObservationSegment (plan.topology.protocol kind).Observation)
      (step : plan.StepsLocally before after kind slot event emitted issued localEmitted)
  /-- A new incarnation appears. -/
  | spawn (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
      (allocation : Allocation plan.topology.Carrier)
      (emitted : Trace boundary.Observation)
      (localEmitted : ObservationSegment (plan.topology.protocol kind).Observation)
      (step : plan.Spawns before after kind slot allocation emitted localEmitted)
  /-- A message enters escrow. -/
  | send (edge : plan.topology.ChannelKind) (message : plan.message edge)
      (occurrence : plan.topology.ChannelOccurrence edge message)
      (step : plan.SendsEscrow before after edge message occurrence)
  /-- The receiver consumes it, advancing its cursor. -/
  | receive (edge session occurrence)
      (step : plan.Delivers before after edge session occurrence)
  /-- Observations processes produced are committed. -/
  | commit (emitted : Trace boundary.Observation)
      (step : plan.Commits before after emitted)
  /-- A cancellation is requested. Escrow is untouched. -/
  | requestCancel (edge session occurrence)
      (step : plan.RequestsCancel before after edge session occurrence)
  /-- And acknowledged, which resolves it. -/
  | acknowledgeCancel (edge session occurrence) (reason : CancelReason)
      (step : plan.ResolvesEscrow before after edge session occurrence
        (.cancelAcknowledged reason))
  /-- It timed out. -/
  | timeout (edge session occurrence)
      (step : plan.ResolvesEscrow before after edge session occurrence .timedOut)
  /-- An instance's outstanding demand was abandoned. -/
  | interrupt (kind slot) (reason : (plan.topology.protocol kind).InterruptReason)
      (custody : Bag (plan.topology.protocol kind).Demand →
        Obligations → Obligations → Prop)
      (step : plan.EndsInstance before after kind slot (.interrupted reason) custody)
  /-- An instance faulted. -/
  | fault (kind slot) (fault : (plan.topology.protocol kind).LogicalFault)
      (custody : Bag (plan.topology.protocol kind).Demand →
        Obligations → Obligations → Prop)
      (step : plan.EndsInstance before after kind slot (.faulted fault) custody)
  /-- Its environment broke a contract. -/
  | environmentViolation (kind slot)
      (violation : (plan.topology.protocol kind).EnvironmentViolation)
      (custody : Bag (plan.topology.protocol kind).Demand →
        Obligations → Obligations → Prop)
      (step : plan.EndsInstance before after kind slot (.violated violation) custody)
  /--
  A **child** acknowledged a cancellation, at this point.

  `wasChild` is the same field `Joins` carries and for the same reason. Without
  it the name is decoration: local adversarial review cancelled the *root*
  through this constructor while building a minimal plan, which is a program
  being stopped by a supervisor it does not have. It also made the frontier
  question unanswerable — any live network could be ended by a step that is not
  entropy-driven, so nothing could be waiting on anything.
  -/
  | childCancelled (kind slot) (reason : CancelReason)
      (custody : Bag (plan.topology.protocol kind).Demand →
        Obligations → Obligations → Prop)
      (wasChild : ∀ incarnation, before.instances kind slot = some incarnation →
        ¬ incarnation.IsRoot)
      (step : plan.EndsInstance before after kind slot (.cancelled reason) custody)
  /-- A **child** stopped existing without finishing. `wasChild` as above. -/
  | childDied (kind slot) (reason : ProcessDeathReason)
      (custody : Bag (plan.topology.protocol kind).Demand →
        Obligations → Obligations → Prop)
      (wasChild : ∀ incarnation, before.instances kind slot = some incarnation →
        ¬ incarnation.IsRoot)
      (step : plan.EndsInstance before after kind slot (.died reason) custody)
  /--
  An instance reached a terminal state of its protocol.

  Unrestricted, and the docstring used to say "a non-child instance" — which is
  wrong, because `Joins.wasTerminated` requires a child to be *already*
  terminated and nothing else can terminate one. A child terminates here and is
  then collected by `join`; the root terminates here and is collected by nobody.
  -/
  | processTermination (kind slot)
      (result : (plan.topology.protocol kind).TerminalResult)
      (custody : Bag (plan.topology.protocol kind).Demand →
        Obligations → Obligations → Prop)
      (step : plan.EndsInstance before after kind slot (.terminated result) custody)
  /-- The session was closed in the ordinary way. -/
  | channelClose (edge session occurrence)
      (step : plan.ClosesSession before after edge session occurrence)
  /-- The sender died. -/
  | senderDeath (edge session occurrence) (reason : ProcessDeathReason)
      (step : plan.ResolvesEscrow before after edge session occurrence (.senderDied reason))
  /-- The receiver died. -/
  | receiverDeath (edge session occurrence) (reason : ProcessDeathReason)
      (step : plan.ResolvesEscrow before after edge session occurrence
        (.receiverDied reason))
  /-- The session died. -/
  | channelDeath (edge session occurrence)
      (step : plan.KillsSession before after edge session occurrence)
  /-- An explicit disposition dropped it. -/
  | drop (edge session occurrence)
      (step : plan.ResolvesEscrow before after edge session occurrence .dropped)
  /-- It moved to another session. -/
  | reroute (edge session occurrence) (destination : plan.topology.ChannelId edge)
      (step : plan.Reroutes before after edge session occurrence destination)
  /-- It merged into another occurrence. -/
  | coalesce (edge session occurrence)
      (carrier : EdgeOccurrence plan.topology plan.message edge)
      (step : plan.ResolvesEscrow before after edge session occurrence (.coalesced carrier))
  /-- A parent joined a finished child. -/
  | join (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
      (result : (plan.topology.protocol kind).TerminalResult)
      (step : plan.Joins before after kind slot result)
  /-- A parent let a child go. -/
  | detach (kind slot) (step : plan.Detaches before after kind slot)
  /-- A supervisor started a fresh incarnation. -/
  | restart (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
      (allocation : Allocation plan.topology.Carrier)
      (emitted : Trace boundary.Observation)
      (localEmitted : ObservationSegment (plan.topology.protocol kind).Observation)
      (step : plan.Restarts before after kind slot allocation emitted localEmitted)

namespace NetworkTransition

variable {plan} {before after : plan.LogicalProcessNetwork}

/--
The fragments a step may have changed.

`docs/PROCESS.md` §8's `TransitionScope step`. Total by construction: the match
is exhaustive over the family, so there is no transition whose scope is
undefined and none that can change a fragment without declaring it.
-/
def scope : plan.NetworkTransition before after → NetworkFragment plan.topology → Prop
  | .processStep kind slot _ emitted _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (emitted ≠ [] ∧ fragment = .pending) ∨
        ∃ region, before.shared region ≠ after.shared region ∧ fragment = .region region
  | .spawn kind slot _ emitted _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨ fragment = .nominals ∨
        (emitted ≠ [] ∧ fragment = .pending)
  | .restart kind slot _ emitted _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨ fragment = .nominals ∨
        (emitted ≠ [] ∧ fragment = .pending)
  | .send edge _ occurrence _ => fun fragment => fragment = .escrow edge occurrence.1
  | .commit emitted _ =>
      fun fragment => emitted ≠ [] ∧ (fragment = .observations ∨ fragment = .pending)
  | .receive edge session _ _ =>
      fun fragment => fragment = .escrow edge session ∨ fragment = .session edge session
  | .requestCancel edge session _ _ => fun fragment => fragment = .escrow edge session
  | .acknowledgeCancel edge session _ _ _ => fun fragment => fragment = .escrow edge session
  | .timeout edge session _ _ => fun fragment => fragment = .escrow edge session
  | .channelClose edge session _ _ =>
      fun fragment => fragment = .escrow edge session ∨ fragment = .session edge session
  | .senderDeath edge session _ _ _ => fun fragment => fragment = .escrow edge session
  | .receiverDeath edge session _ _ _ => fun fragment => fragment = .escrow edge session
  | .channelDeath edge session _ _ =>
      fun fragment => fragment = .escrow edge session ∨ fragment = .session edge session
  | .drop edge session _ _ => fun fragment => fragment = .escrow edge session
  | .reroute edge session _ destination _ =>
      fun fragment => fragment = .escrow edge session ∨ fragment = .escrow edge destination
  | .coalesce edge session _ _ _ => fun fragment => fragment = .escrow edge session
  | .interrupt kind slot _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (before.obligations ≠ after.obligations ∧ fragment = .obligations)
  | .fault kind slot _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (before.obligations ≠ after.obligations ∧ fragment = .obligations)
  | .environmentViolation kind slot _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (before.obligations ≠ after.obligations ∧ fragment = .obligations)
  | .childCancelled kind slot _ _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (before.obligations ≠ after.obligations ∧ fragment = .obligations)
  | .childDied kind slot _ _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (before.obligations ≠ after.obligations ∧ fragment = .obligations)
  | .processTermination kind slot _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (before.obligations ≠ after.obligations ∧ fragment = .obligations)
  | .join kind slot _ _ => fun fragment => fragment = .instanceState kind slot
  | .detach kind slot _ => fun fragment => fragment = .instanceState kind slot

/--
A step driven by entropy from outside the program.

`ProcessEvent.externalEntropy` lifted to a transition, and the distinction
`Grass/Process/Network/Progress.lean` needs to tell a network *waiting* on the
environment from one *spinning*: a frontier is a place only the outside world
can move you off.

A `processStep` qualifies when its event *arrived from outside* — entropy, or a
result to a demand the process is waiting on — and a `timeout` qualifies
outright. Three drafts of that clause were wrong, in three different directions.

**It was too narrow.** §7 asks a plan to "reach a law-bearing
external/**demand-result** frontier", and the step that leaves a demand-result
frontier is a `processStep` on `.result`, whose `externalEntropy` is `none`. So
a network blocked on a boundary demand could not be declared at a frontier at
all, and a reactive plan that services requests forever without emitting a
demanded observation had no `NetworkProgressMeasure` — the measure was
unconstructible rather than merely hard.

**And too wide.** `environmentViolation` was in the list.
`Grass/Process/Vocabulary.lean` proves
`(ProcessEvent.environmentViolation v).externalEntropy = none`, and
`Grass/Process/Progress.lean`'s `silent_nonentropy_step_decreases` says the
per-process layer changed from `settles` to `externalEntropy` precisely so that
faults and environment violations stop buying progress for free. Handing it back
at the network was inconsistent with that, and internally inconsistent too: a
`processStep` carrying `.environmentViolation` was not entropy-driven while the
`environmentViolation` *constructor* was — the same occurrence classified two
ways by which constructor a plan routed it through.

**And too wide again, in the repair.** The fix for the first was
`event.settles ≠ none`, and `settles` is `some` for `.interrupted` as well as
for `.result`. An interruption is a process abandoning *its own* outstanding
demand, which §2 calls an internal decision — so the repair reintroduced exactly
the defect the paragraph above removes, one constructor over: a `processStep`
carrying `.interrupted` was entropy-driven while `NetworkTransition.interrupt`,
which records the same abandonment as an ending, was not. At `countdown` it had
teeth, because `Step` on `.interrupted` decrements the counter — a network could
grind its own state down through steps a frontier excuses.

`ProcessEvent.arrivesFromOutside` is the split that is actually wanted, and it is
neither of the two the vocabulary already had. All three were found by local
adversarial review, each after the previous repair landed.

What remains open: a `.result` may be answered by a child rather than by the
driver, and this cannot tell them apart — `rootLocalDemandProjection` exists only
for the root's protocol. That makes the predicate slightly wider than "the
outside must act", and `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.44 records it.
-/
def DrivenByEntropy : plan.NetworkTransition before after → Prop
  | .processStep _ _ event _ _ _ _ => event.arrivesFromOutside
  | .timeout _ _ _ _ => True
  | _ => False

/--
**Routing coverage: every step respects the scope it declares.**

`docs/PROCESS.md` §3's "no fabrication, bypass, or unclassified death is
possible", in the form this layer can state: a transition is a constructor, every
constructor determines a `scope`, and every one of them changed nothing outside
it. There is no path through the family that reaches a fragment without
declaring it, because the proof is by cases over the whole family and each case
is the step's own scope field.

This is what makes `Grass/Process/Network/Channel.lean`'s framing usable at a
weave: `docs/PROCESS.md` §8's `Disjoint (TransitionScope step) Scope` now has a
`TransitionScope` to be disjoint from.
-/
theorem touchesOnly (transition : plan.NetworkTransition before after) :
    plan.TouchesOnly before after transition.scope := by
  cases transition with
  | processStep _ _ _ _ _ _ step => exact step.scope
  | spawn _ _ _ _ _ step => exact step.scope
  | restart _ _ _ _ _ step => exact step.scope
  | send _ _ _ step => exact step.scope
  | commit _ step => exact step.scope
  | receive _ _ _ step => exact step.scope
  | requestCancel _ _ _ step => exact step.scope
  | acknowledgeCancel _ _ _ _ step => exact step.scope
  | timeout _ _ _ step => exact step.scope
  | channelClose _ _ _ step => exact step.scope
  | senderDeath _ _ _ _ step => exact step.scope
  | receiverDeath _ _ _ _ step => exact step.scope
  | channelDeath _ _ _ step => exact step.scope
  | drop _ _ _ step => exact step.scope
  | reroute _ _ _ _ step => exact step.scope
  | coalesce _ _ _ _ step => exact step.scope
  | interrupt _ _ _ _ step => exact step.scope
  | fault _ _ _ _ step => exact step.scope
  | environmentViolation _ _ _ _ step => exact step.scope
  | childCancelled _ _ _ _ _ step => exact step.scope
  | childDied _ _ _ _ _ step => exact step.scope
  | processTermination _ _ _ _ step => exact step.scope
  | join _ _ _ step => exact step.scope
  | detach _ _ step => exact step.onlyThatSlot.scope

/--
**The obligation ledger moves only where a process ends.**

`docs/PROCESS.md` §2: "termination explicitly resolves, transfers, or permits
pending". This is that as a fact about every execution rather than about one
transition: a step that changed the ledger was an `EndsInstance`, and the ending
is not `.running`.

The `EndsInstance` witness carries the rest — `custodyDeclared` says the ending's
declared custody admits the new ledger, admits nothing else, and is indexed by
the bag the ending was holding. Those are read off the witness rather than
restated here, because an earlier version *did* restate them and the restatement
was weaker than the fields: it existentially quantified a custody relation, and
`fun _ _ => True` satisfies an existential for any movement whatsoever.

`ending ≠ .running` is likewise the field rather than a derivation. Without it
this theorem reported a still-live process as having ended, which local
adversarial review demonstrated at a plan with two obligation values.

The proof is by cases over the whole family and the eighteen non-ending cases
are all the same: `.obligations` is not in their scope, so `touchesOnly` gives
equality and contradicts the hypothesis.

Worth noting what this replaced. Until `EndsInstance` carried a custody
parameter, *no* constructor named `.obligations` in its scope, so the ledger
`Grass/Process/Network/World.lean` deliberately parameterises could never move
at all — and this theorem would have been true for the wrong reason, with an
unsatisfiable hypothesis. `docs/FOUNDATION.md` law 7 had nothing to bite on.
-/
theorem moving_the_ledger_ends_an_instance (transition : plan.NetworkTransition before after)
    (moved : before.obligations ≠ after.obligations) :
    ∃ (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
      (ending : ProcessLifecycle (plan.topology.protocol kind))
      (custody : Bag (plan.topology.protocol kind).Demand →
        Obligations → Obligations → Prop),
      plan.EndsInstance before after kind slot ending custody ∧ ending ≠ .running := by
  cases transition with
  | interrupt kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.notRunning⟩
  | fault kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.notRunning⟩
  | environmentViolation kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.notRunning⟩
  | childCancelled kind slot _ custody _ step =>
    exact ⟨kind, slot, _, custody, step, step.notRunning⟩
  | childDied kind slot _ custody _ step =>
    exact ⟨kind, slot, _, custody, step, step.notRunning⟩
  | processTermination kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.notRunning⟩
  | processStep _ _ _ _ _ _ step =>
    exact absurd (step.scope .obligations (by simp)) moved
  | spawn _ _ _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | restart _ _ _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | send _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | commit _ step => exact absurd (step.scope .obligations (by simp)) moved
  | receive _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | requestCancel _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | acknowledgeCancel _ _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | timeout _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | channelClose _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | senderDeath _ _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | receiverDeath _ _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | channelDeath _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | drop _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | reroute _ _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | coalesce _ _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | join _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | detach _ _ step => exact absurd (step.onlyThatSlot.scope .obligations (by simp)) moved

/--
The nominals a step allocates.

`docs/PROCESS.md` §3: "definitionally empty for nonallocating transitions". Two
constructors allocate — `spawn` and `restart` — and both carry the allocation
whose entries `Spawns.allocatesTheGeneration` requires to contain the new
incarnation's generation. Every other case is `Allocation.empty` by definition,
not by a proof.
-/
def allocatedNominals :
    plan.NetworkTransition before after → Allocation plan.topology.Carrier
  | .spawn _ _ allocation _ _ _ => allocation
  | .restart _ _ allocation _ _ _ => allocation
  | _ => Allocation.empty

@[simp] theorem allocatedNominals_receive {edge session occurrence step} :
    (NetworkTransition.receive (plan := plan) (before := before) (after := after)
      edge session occurrence step).allocatedNominals = Allocation.empty := rfl

@[simp] theorem allocatedNominals_commit {emitted step} :
    (NetworkTransition.commit (plan := plan) (before := before) (after := after)
      emitted step).allocatedNominals = Allocation.empty := rfl

end NetworkTransition

/--
**A step of an execution: a transition, plus the freshness law.**

`docs/PROCESS.md` §3's `NetworkStep`. `admissible` is its `fresh` — every
allocated identity was absent from the monotone history, which
`Grass/Process/Nominal.lean` defines as absence from `used` and not from a live
set — and `historyExact` is its union equation.

`Grass/Process/Nominal.lean` already carried `Allocation`, `Fresh`, `Admissible`
and `extend`, so this is thin. What makes it more than a wrapper is
`Spawns.allocatesTheGeneration`: without it a spawn could allocate nothing while
installing a fresh generation, and the freshness law would range over an
allocation unrelated to what the step introduced.
-/
structure NetworkStep (before after : plan.LogicalProcessNetwork) where
  /-- Which step. -/
  transition : plan.NetworkTransition before after
  /-- Everything it allocates was fresh. -/
  admissible : before.usedNominals.Admissible transition.allocatedNominals
  /-- And the history afterwards is exactly the union. -/
  historyExact :
    after.usedNominals = before.usedNominals.extend transition.allocatedNominals admissible

namespace NetworkStep

variable {plan} {before after : plan.LogicalProcessNetwork}

/-- A step changed nothing outside its transition's scope. -/
theorem touchesOnly (step : plan.NetworkStep before after) :
    plan.TouchesOnly before after step.transition.scope :=
  step.transition.touchesOnly

/--
**An identity allocated by this step was never allocated before it.**

Law 22 at the step: freshness is absence from the history, so an identity this
step introduces cannot be one a resolved or tombstoned occurrence already used.
-/
theorem allocations_were_fresh (step : plan.NetworkStep before after)
    {nominal} (allocated : nominal ∈ step.transition.allocatedNominals.entries) :
    before.usedNominals.Fresh nominal :=
  step.admissible nominal allocated

/-- And it is in the history afterwards, so no later step can allocate it again. -/
theorem allocations_are_recorded (step : plan.NetworkStep before after)
    {nominal} (allocated : nominal ∈ step.transition.allocatedNominals.entries) :
    nominal ∈ after.usedNominals.used := by
  rw [step.historyExact]
  exact NominalHistory.mem_extend.mpr (Or.inl allocated)

/-- A non-allocating step leaves the history exactly as it was. -/
theorem nonallocating_preserves_history (step : plan.NetworkStep before after)
    (nothing : step.transition.allocatedNominals = Allocation.empty) :
    after.usedNominals = before.usedNominals := by
  rw [step.historyExact]
  simp [nothing]

end NetworkStep

end ProcessPlan

end Grass.Process
