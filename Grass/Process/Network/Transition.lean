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
`StepsLocally` above.

`statusUnchanged` is what keeps the widening honest: a delivery advances the
cursor and does not close a channel, so a caller reading the status still learns
something from it.
-/
structure Delivers (before after : plan.LogicalProcessNetwork)
    (edge : plan.topology.ChannelKind) (session : plan.topology.ChannelId edge)
    (occurrence : EdgeOccurrence plan.topology plan.message edge) : Prop where
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
    (ending : ProcessLifecycle (plan.topology.protocol kind))
    (custody : Obligations → Obligations → Prop) : Prop where
  /-- It was live. -/
  wasLive : ∃ incarnation, before.instances kind slot = some incarnation ∧
    incarnation.Live
  /-- It now carries exactly this ending. -/
  nowEnded : ∃ incarnation, after.instances kind slot = some incarnation ∧
    ∃ sameKind : incarnation.kind = kind, sameKind ▸ incarnation.lifecycle = ending
  /--
  **And the obligation ledger moves exactly as this ending declared.**

  `docs/PROCESS.md` §2: "termination explicitly resolves, transfers, or permits
  pending". `custody` is a parameter rather than a field, so it is the
  *constructor* that names the transfer and a reader of the transition sees it —
  the same trade as `written` on `StepsLocally` and `emitted` on `Commits`.

  Before this existed, no constructor of `NetworkTransition` named
  `.obligations` in its scope, so by `touchesOnly` the ledger
  `Grass/Process/Network/World.lean` deliberately parameterises could never move
  in any program at all. A weave mixin about obligations framed past every step
  vacuously, and §7's `DisjointOrCommutingObligations` was satisfied by the
  whole family for free.
  -/
  custodyDeclared : custody before.obligations after.obligations
  /--
  **And the declared custody determines where the ledger went.**

  `custodyDeclared` on its own is satisfied by `custody := fun _ _ => True`, so
  a constructor could declare a transfer and mean nothing by it — local
  adversarial review pointed out that the theorem below then existentially
  quantifies a relation `True` satisfies, and its "the ending carries the
  custody relation the change satisfies" was decoration.

  This is the same move `Grass/Process/Function/Serial.lean` makes with
  `SerialFunctionRealizes.converse`: requiring the declared relation to be
  single-valued at the before-state turns it from a claim the author can make
  vacuously into one that pins the outcome. At any plan whose `Obligations` has
  two values, `fun _ _ => True` is now refuted.
  -/
  custodyExact : ∀ other, custody before.obligations other → other = after.obligations
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
    (ended : plan.EndsInstance before after kind slot ending custody)
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
    (written : plan.topology.SharedRegion → Prop)
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

  With it, the four things §3 requires of a local step are here: the protocol
  admits the transition, the demands it issues are the protocol's own, the
  observation segment is the one the protocol emitted, and the issued bag
  reaches the instance's outstanding demands by §2's linear equation
  (`SettlesDemands`) rather than being discarded.
  -/
  protocolStep : ∃ (fromInstance toInstance : ProcessInstance plan.topology)
      (fromKind : fromInstance.kind = kind) (toKind : toInstance.kind = kind),
    before.instances kind slot = some fromInstance ∧
    after.instances kind slot = some toInstance ∧
    (plan.topology.protocol kind).Step (fromKind ▸ fromInstance.localState) event
      (toKind ▸ toInstance.localState) issued localEmitted ∧
    plan.SettlesDemands event issued (fromKind ▸ fromInstance.outstanding)
      (toKind ▸ toInstance.outstanding)
  /--
  **And what reaches the network trace is the projection of what it observed.**

  `ProcessGraph.observeAt` is the declaration; this is where it is spent. Before
  it, `emitted` was an arbitrary boundary segment: a step could append anything
  to the program's trace regardless of what the role observed.
  -/
  emittedIsProjected : emitted = localEmitted.filterMap (plan.topology.observeAt kind)
  /-- Observations grow by exactly this segment. -/
  observationsExtend : after.observations = before.observations ++ emitted
  /--
  **And it writes only regions its role may write.**

  `docs/PROCESS.md` §3: shared logical state is "named separately with
  read/write/atomic capabilities", and this is where that capability is spent
  rather than merely declared.
  -/
  writesPermitted : ∀ region, written region →
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
      (emitted ≠ [] ∧ fragment = .observations) ∨
      ∃ region, written region ∧ fragment = .region region)

/--
A new incarnation appears in a slot that was empty.

`allocation` is what `docs/PROCESS.md` §3 calls the transition's
`allocatedNominals`, and `allocatesTheGeneration` is the correspondence §10.18
records as missing everywhere else: the identity the spawned instance carries is
one this step allocated, so the history cannot omit it.
-/
structure Spawns (before after : plan.LogicalProcessNetwork)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
    (allocation : Allocation plan.topology.Carrier) : Prop where
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
  /-- That slot and the nominal history, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .instanceState kind slot ∨ fragment = .nominals)

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
    (allocation : Allocation plan.topology.Carrier) : Prop where
  /-- **The slot held an incarnation that had ended.** -/
  wasEnded : ∃ incarnation, before.instances kind slot = some incarnation ∧
    ¬ incarnation.Live
  /-- It now holds a live incarnation of the right kind. -/
  nowLive : ∃ incarnation, after.instances kind slot = some incarnation ∧
    incarnation.Live ∧ incarnation.kind = kind
  /-- Whose generation this step allocated — a restart is a new incarnation. -/
  allocatesTheGeneration : ∀ incarnation, after.instances kind slot = some incarnation →
    incarnation.ref.generation ∈ allocation.entries
  /-- That slot and the nominal history, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => fragment = .instanceState kind slot ∨ fragment = .nominals)

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
producible by nothing, and a channel that had died kept whatever status it had —
usually `.open`, so `ChannelContract.sendOnOpenSession` still admitted sends on
it.
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
  /-- The request is recorded. -/
  nowRequested : (after.inFlight edge session).cancelRequested occurrence = true
  /-- **And it is still in flight.** -/
  stillOutstanding : (after.inFlight edge session).Outstanding occurrence
  /-- That session's escrow, and nothing else. -/
  scope : plan.TouchesOnly before after (fun fragment => fragment = .escrow edge session)

/--
A commit appends to the observation trace.

`docs/PROCESS.md` §6's transition, at the only fragment it touches. Appending
rather than replacing is the content: a trace that could be rewritten would let
a reconciler drop an observation a specification demanded.
-/
structure Commits (before after : plan.LogicalProcessNetwork)
    (emitted : Trace boundary.Observation) : Prop where
  /-- The trace grew by exactly this much. -/
  appended : after.observations = before.observations ++ emitted
  /-- The observation trace **if it actually appended**, and nothing else. -/
  scope : plan.TouchesOnly before after
    (fun fragment => emitted ≠ [] ∧ fragment = .observations)

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
  /-- It no longer does, and remembers which. -/
  nowDetached : ∃ incarnation, after.instances kind slot = some incarnation ∧
    incarnation.IsDetached ∧ incarnation.parentage.knownParent ≠ none
  /-- That slot, and nothing else. -/
  onlyThatSlot : plan.ChangesOneInstance before after kind slot

namespace Detaches

variable {plan}

/-- A detached child keeps a recorded former parent, which is what makes
`Grass/Process/Network/Child.lean`'s `NonReturningReason.detached` checkable. -/
theorem former_parent_is_recorded {before after kind slot}
    (detached : plan.Detaches before after kind slot) :
    ∃ incarnation, after.instances kind slot = some incarnation ∧
      incarnation.parentage.knownParent ≠ none := by
  obtain ⟨incarnation, found, _, remembered⟩ := detached.nowDetached
  exact ⟨incarnation, found, remembered⟩

end Detaches

/--
**One step of a logical process network.**

`docs/PROCESS.md` §3's twenty-three constructors. Ten of them are the competing
escrow resolutions and share `ResolvesEscrow`, distinguished by the resolution
each writes; the rest carry the shape their own effect needs.

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
      (written : plan.topology.SharedRegion → Prop)
      (emitted : Trace boundary.Observation)
      (issued : Bag (plan.topology.protocol kind).Demand)
      (localEmitted : ObservationSegment (plan.topology.protocol kind).Observation)
      (step : plan.StepsLocally before after kind slot event written emitted
        issued localEmitted)
  /-- A new incarnation appears. -/
  | spawn (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
      (allocation : Allocation plan.topology.Carrier)
      (step : plan.Spawns before after kind slot allocation)
  /-- A message enters escrow. -/
  | send (edge : plan.topology.ChannelKind) (message : plan.message edge)
      (occurrence : plan.topology.ChannelOccurrence edge message)
      (step : plan.SendsEscrow before after edge message occurrence)
  /-- The receiver consumes it, advancing its cursor. -/
  | receive (edge session occurrence)
      (step : plan.Delivers before after edge session occurrence)
  /-- Observations are committed. -/
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
      (custody : Obligations → Obligations → Prop)
      (step : plan.EndsInstance before after kind slot (.interrupted reason) custody)
  /-- An instance faulted. -/
  | fault (kind slot) (fault : (plan.topology.protocol kind).LogicalFault)
      (custody : Obligations → Obligations → Prop)
      (step : plan.EndsInstance before after kind slot (.faulted fault) custody)
  /-- Its environment broke a contract. -/
  | environmentViolation (kind slot)
      (violation : (plan.topology.protocol kind).EnvironmentViolation)
      (custody : Obligations → Obligations → Prop)
      (step : plan.EndsInstance before after kind slot (.violated violation) custody)
  /-- A child ended, with the exact result decision 129 stores. -/
  | childLifecycle (kind slot)
      (ending : ProcessLifecycle (plan.topology.protocol kind))
      (custody : Obligations → Obligations → Prop)
      (step : plan.EndsInstance before after kind slot ending custody)
  /-- A non-child instance terminated. -/
  | processTermination (kind slot)
      (result : (plan.topology.protocol kind).TerminalResult)
      (custody : Obligations → Obligations → Prop)
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
      (step : plan.Restarts before after kind slot allocation)

namespace NetworkTransition

variable {plan} {before after : plan.LogicalProcessNetwork}

/--
The fragments a step may have changed.

`docs/PROCESS.md` §8's `TransitionScope step`. Total by construction: the match
is exhaustive over the family, so there is no transition whose scope is
undefined and none that can change a fragment without declaring it.
-/
def scope : plan.NetworkTransition before after → NetworkFragment plan.topology → Prop
  | .processStep kind slot _ written emitted _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (emitted ≠ [] ∧ fragment = .observations) ∨
        ∃ region, written region ∧ fragment = .region region
  | .spawn kind slot _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨ fragment = .nominals
  | .restart kind slot _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨ fragment = .nominals
  | .send edge _ occurrence _ => fun fragment => fragment = .escrow edge occurrence.1
  | .commit emitted _ => fun fragment => emitted ≠ [] ∧ fragment = .observations
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
  | .childLifecycle kind slot _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (before.obligations ≠ after.obligations ∧ fragment = .obligations)
  | .processTermination kind slot _ _ _ =>
      fun fragment => fragment = .instanceState kind slot ∨
        (before.obligations ≠ after.obligations ∧ fragment = .obligations)
  | .join kind slot _ _ => fun fragment => fragment = .instanceState kind slot
  | .detach kind slot _ => fun fragment => fragment = .instanceState kind slot

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
  | processStep _ _ _ _ _ _ _ step => exact step.scope
  | spawn _ _ _ step => exact step.scope
  | restart _ _ _ step => exact step.scope
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
  | childLifecycle _ _ _ _ step => exact step.scope
  | processTermination _ _ _ _ step => exact step.scope
  | join _ _ _ step => exact step.scope
  | detach _ _ step => exact step.onlyThatSlot.scope

/--
**The obligation ledger moves only where a process ends, and only where that
ending's declared custody sent it.**

`docs/PROCESS.md` §2: "termination explicitly resolves, transfers, or permits
pending". This is that as a fact about every execution rather than about one
transition: a step that changed the ledger *was* an ending, and the ending's
declared custody both admits the new ledger (`custodyDeclared`) and admits
nothing else (`custodyExact`).

The second conjunct is what an earlier version's docstring claimed and its
statement did not deliver: with only `custodyDeclared`, the existential is
satisfied by `custody := fun _ _ => True` for any movement whatsoever.

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
      (custody : Obligations → Obligations → Prop),
      plan.EndsInstance before after kind slot ending custody ∧
        custody before.obligations after.obligations ∧
        ∀ other, custody before.obligations other → other = after.obligations := by
  cases transition with
  | interrupt kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.custodyDeclared, step.custodyExact⟩
  | fault kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.custodyDeclared, step.custodyExact⟩
  | environmentViolation kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.custodyDeclared, step.custodyExact⟩
  | childLifecycle kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.custodyDeclared, step.custodyExact⟩
  | processTermination kind slot _ custody step =>
    exact ⟨kind, slot, _, custody, step, step.custodyDeclared, step.custodyExact⟩
  | processStep _ _ _ _ _ _ _ step =>
    exact absurd (step.scope .obligations (by simp)) moved
  | spawn _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
  | restart _ _ _ step => exact absurd (step.scope .obligations (by simp)) moved
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
  | .spawn _ _ allocation _ => allocation
  | .restart _ _ allocation _ => allocation
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
