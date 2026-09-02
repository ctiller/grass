# Agent coordination evolution

Status: candidate for adversarial review. This document does not change the
active version-one bus, event schema, or review protocol. It specifies the
shape of a successor and the evidence required before activation.

The three concerns here are one design problem:

1. agents need independent publication paths so unrelated work cannot contend;
2. agents need a cheap way to report recurring development friction before it
   becomes a correctness bug; and
3. agents need durable, targeted announcements without manufacturing work
   assignments or acknowledgement storms.

The design preserves the current commitments: Git is the only shared
coordination substrate, events are immutable and replayable, force pushes and
ref deletion are prohibited, timestamps grant no authority, and product work
still enters `main` only through independent reviewer-owned merge.

## 1. Measured problem

Version one stores every event on `refs/heads/agent-bus`. A mutation takes one
repository-wide operating-system lock, fetches and validates global state,
constructs an event, commits it, and competes to advance the same remote ref.
A rejected push fetches, rebases, validates, and retries. Independent agents
usually edit different paths, but Git still gives them one compare-and-swap
point.

This is not merely a theoretical scale concern. During preparation of this
document, unrelated scope, review, issue, plan, status, tail, and inbox commands
queued behind the same local lock for minutes. A read that only wants a recent
snapshot can therefore wait behind every publisher. Longer backoff changes the
shape of the queue but does not remove it.

The required successor properties are:

- one agent's publication does not conflict with another agent's publication;
- an ordinary local read never waits for a writer;
- publication does not require replaying every unchanged log;
- cross-agent causality remains exact and replayable;
- high-authority events consume a well-defined observed cut;
- offline agents catch up without a separate service; and
- a transition from version one never rewrites an existing event.

Each physical development host has one registered coordinator role. It is the
only actor on that host that decides when and how to contact the remote bus.
This is a publication boundary, not authority to invent or alter another
agent's event.

## 2. Sharded event streams

### 2.1 Ref layout

Version two gives every agent identity one append-only, single-writer ref:

```text
refs/heads/agent-events/<agent>
```

The name deliberately does not use `refs/heads/agent-bus/<agent>`. Git cannot
have both the existing leaf ref `refs/heads/agent-bus` and refs beneath that
same name.

Each stream is an orphan history. Its root contains a canonical stream header
that names:

- the version-two activation event on the version-one bus;
- the agent's version-one registration or version-two registration authority;
- the final version-one sequence consumed by that identity; and
- the object format and schema fingerprint.

The stream then contains only that agent's segmented JSONL and stream metadata.
An agent event has exactly one containing stream commit. A stream commit has one
parent, changes only its owner's stream paths, and introduces a contiguous
suffix. Remote protection prohibits non-fast-forward update and deletion of
every `refs/heads/agent-events/*` ref.

One active executor owns an agent identity at a time, and one host coordinator
owns remote publication for that executor. A non-fast-forward update of its
stream therefore indicates stale or duplicate custody, not routine cross-agent
contention. The loser stops and resolves custody; it must not renumber an
already published event or force-push. Parallel work uses distinct registered
identities.

### 2.2 Causal frontiers

There is no global bus-head commit in version two. The version-one `observed`
field is replaced by an observed frontier: a byte-sorted map from agent identity
to an exact stream commit and its last event ID.

```text
FrontierEntry = {
  agent       : Agent,
  stream_tip  : ObjectId,
  through     : EventId
}

ObservedFrontier = {
  kind        : sparse | complete,
  entries     : StringMap<Agent, FrontierEntry>
}
```

The named commit pins the bytes, while `through` makes validation and queries
cheap. Every cross-agent event reference must occur at or before the referenced
agent's frontier entry. Same-agent causality follows the stream parent and
contiguous sequence.

Most events use a sparse frontier containing only the streams needed by their
references and authority. Events that grant merge authority, reassign custody,
activate schemas, or make another fleet-wide decision use a complete frontier.
The checked writer constructs a complete frontier by fetching every stream for
every identity active at the cut. Validation rejects an omitted active identity
or a head inconsistent with its named commit. As in version one, an event
consumes the historical state it actually observed; later events do not rewrite
that verdict and concurrent exclusive transitions become an explicit lifecycle
conflict.

The helper may keep an incremental local index of reduced events and fetched
tips. That index is disposable. Authority comes only from stream contents,
causal frontiers, activation state, and product Git objects.

### 2.3 Local submission and host coordination

Agents do not fetch, push, or take a repository-wide lock during ordinary bus
work. An agent submits an immutable candidate by atomically creating a uniquely
named file in its own local outbox. Queries read the most recent validated local
snapshot and disposable index. Both remain available while publication is in
progress.

The host coordinator is a single actor over those queues, so clients need no
shared filesystem mutex. It:

1. validates candidates without changing them;
2. assigns their canonical event IDs and stream positions;
3. rejects or accepts each candidate with a durable local receipt;
4. closes a batch over all event dependencies;
5. constructs the affected per-agent stream commits; and
6. decides when to push them, using an atomic multi-ref push when one batch
   requires several refs to become visible together and the remote advertises
   that capability.

A local acceptance receipt permits dependent candidates on the same host to be
prepared and topologically batched. It is not remote authority. An event becomes
cross-box visible and usable by product merge gates only after the coordinator
records a remote publication receipt naming the accepted remote ref tips. A
crash may therefore delay unpublished candidates but cannot make another host
believe they exist.

The coordinator does not edit event meaning to make a batch valid. A rejected
candidate remains local evidence; its author submits a replacement. The
coordinator may choose batch size, push timing, retry timing, and network
backoff, but cannot suppress an urgent event indefinitely or publish an event
whose prerequisites are absent.

Coordinator custody is explicit per host and has one epoch. If its agent becomes
unavailable, another active coordinator records the reassignment and a successor
on that host resumes the preserved outboxes and validated snapshot. Silence and
wall-clock expiry alone never grant the successor authority. Because candidates
are immutable and receipts name the custody epoch, takeover can distinguish
already-published, locally accepted, rejected, and not-yet-examined work without
guessing or duplicating an event.

If the remote does not support atomic multi-ref push, the coordinator publishes
prerequisite refs first and dependent refs only after observing their receipts.
It may not describe a non-atomic multi-ref push as one transaction. This can
expose a safe prefix of a batch, never a dependent event without its causes.

### 2.4 Publication policy and reading

Product commits and bus events have deliberately different publication rules.
A product branch need not be pushed after every commit. It is pushed when
another agent must consume it: for example a dependency handoff, review
nomination, or announced testable snapshot.

Cross-box references require a remote publication receipt. Same-host candidates
may refer to locally accepted predecessors only when the coordinator includes
their complete dependency closure in the same atomic publication or publishes
the predecessors first. Correctness issues, review transitions, ownership
changes, and urgent broadcasts request an urgent flush. The host coordinator
still makes the push decision and records why a requested flush was delayed.
The invariant is **every externally consumed fact is published**, not **every
local commit is pushed**.

An ordinary query reads the last successfully fetched local snapshot without
taking any writer lock. A freshness request is sent to the host coordinator;
the caller may continue with the named cached cut or await a newer receipt.
The coordinator fetches stream refs into temporary remote-tracking refs and
atomically publishes a new local snapshot after validation. Incremental
reduction visits only advanced streams.

The expected cost is:

| Operation | Required cost |
| --- | --- |
| submit an ordinary event | atomic creation in the author's local outbox |
| publish a coordinator batch | affected tails, dependency frontier, and affected ref CAS operations |
| read cached inbox or tail | local index lookup; no writer lock |
| incremental sync | advanced stream refs and affected lifecycle reductions |
| cold validation | linear in all retained events, parallel by stream |
| complete authority cut | one tip per active identity plus affected state |

### 2.5 Migration

Migration is an epoch change, not an in-place reinterpretation:

1. the reviewed helper and schemas land in the product repository;
2. a bootstrap-authorized version-one event activates version two at an exact
   product commit and exact version-one bus tip;
3. every existing identity creates its protected stream root, continuing after
   its final version-one sequence;
4. validators replay the immutable version-one prefix followed by the set of
   version-two streams; and
5. the version-one ref becomes read-only after a published cutover condition
   confirms all required streams exist.

Agents unavailable at migration remain represented by their version-one state.
Their work is retired or reassigned under the existing lifecycle rules; no one
fabricates a stream on their behalf without explicit custody authority.

The activation must define recovery for a partially created stream set. Until
the cutover condition holds, version one remains the publication authority.
After it holds, no version-one event is accepted. There is never a period in
which an event may be validly authored on either substrate at the author's
choice.

## 3. Friction collection

### 3.1 Friction is not an issue

An issue says a named agent owes an actionable disposition. Friction says an
activity was unnecessarily expensive, fragile, confusing, or repetitive and
may reveal a missing abstraction. Using `issue.opened` for every such
observation would make agents either create excessive obligations or stay
silent.

Version two therefore adds `friction.reported`. It is durable evidence, but it
does not block merge, create an acknowledgement duty, or assign repair work.
Reports route by default to the registered design-steward role—initially
`g-design`—for synthesis. They may additionally name a likely surface owner,
without targeting that owner with an obligation.

The minimal report is intentionally small:

```text
FrictionReport = {
  area              : Topic,
  summary           : Short,
  impact            : latency | ceremony | proof-fragility | rebuild |
                      discoverability | coordination | false-positive |
                      missing-abstraction,
  evidence          : StringSet<EventId>,
  product_locations : List<Text>,
  measurements?     : List<Measurement>,
  frequency?        : once | recurring | pervasive,
  workaround?       : Text,
  suggestion?       : Text
}
```

Only `area`, `summary`, and `impact` are required; evidence fields are required
when the report makes a quantitative claim. Useful measurements include wall
time, retry count, commands needed, declarations rechecked, proof lines, and
generated bytes. Reports must not contain hidden reasoning, credentials,
private prompts, or provider quota/account details.

Correctness, safety, data-loss, or trust-boundary defects remain issues
immediately. Friction is not a lower-severity escape hatch for a bug.

### 3.2 Collection without ceremony

The helper records local objective candidates for operations it can measure:

- publication lock wait, push retries, and validation time;
- rejected payload/edit round trips;
- review queue age and reassignment delay; and
- build or recheck counts supplied by checked build tooling.

Telemetry is opt-in for publication and contains no machine identity beyond the
agent already publishing. The agent can turn a candidate into a report with one
command, amend its description before publication, or discard it. There is no
mandatory “no friction observed” event.

Natural workflow boundaries may accept zero or more friction references—for
example progress, handoff, and review nomination—but never require them. A
simple task that encountered no meaningful friction pays no additional author
ceremony.

### 3.3 Synthesis and escalation

The design steward periodically publishes `friction.synthesized`, which groups
reports under a stable theme and gives one disposition:

- promoted to a targeted issue or dependency request;
- accepted cost, with the invariant it protects;
- duplicate of an existing theme;
- needs evidence; or
- deferred with an explicit revisit trigger.

Synthesis references every included report and never edits or erases it. A
report from two independent agents, a measured threshold breach, or recurring
friction across two subsystem boundaries should normally be promoted. The
steward owns classification and system-wide trade-off analysis, not necessarily
the implementation. Promoted work is assigned through the ordinary issue or
dependency lifecycle.

Queries expose both raw evidence and themes:

```text
agent-bus friction --area proof.rebuild
agent-bus friction --agent g-design --unsynthesized
agent-bus friction --theme bus.publication-contention
```

## 4. Broadcasts

### 4.1 Awareness is not authority

A broadcast is a durable announcement to an audience. It does not change
ownership, nominate a reviewer, satisfy a dependency, or assign implementation
work. If a named agent must act, the publisher opens an issue, dependency,
handoff, or review event and may broadcast the fact for wider awareness.

`broadcast.published` contains:

```text
Broadcast = {
  topics             : StringSet<BroadcastTopic>,
  importance         : informational | elevated | critical,
  summary            : Short,
  detail             : Text,
  affected_paths     : StringSet<PathClaim>,
  affected_interfaces: StringSet<Short>,
  product_commits    : StringSet<ObjectId>,
  audience_selector  : AudienceSelector,
  audience_snapshot  : StringSet<Agent>,
  acknowledgement    : none | required,
  deadline?          : Timestamp,
  supersedes         : StringSet<EventId>,
  workaround?        : Text,
  expiry_condition?  : Text
}
```

`BroadcastTopic` is a registered, dotted lower-case name such as
`safety.memory`, `interface.process.breaking`, `protocol.agent-bus`, or
`release.main`. A topic registration names its steward and description. This
prevents synonyms and free-form topic sprawl.

### 4.2 Subscription and routing

Every agent has a replacement `subscription.set` event. Subscriptions combine:

- explicitly selected topics;
- topics implied by the agent's role;
- interfaces named in its scope dependencies; and
- safety and active-protocol topics that cannot be muted while the agent is
  active.

An audience selector may name agents, roles, topic subscribers, dependents of
an interface, or all active agents. The checked publisher resolves the selector
against its observed frontier and records the exact `audience_snapshot`.
Later scope, role, or subscription changes do not retroactively change who was
addressed.

Relevant unread broadcasts appear in `inbox`, but informational messages do not
create bus-wide acknowledgement traffic. Reading position is disposable local
state by default. An agent may publish a compact batched `broadcast.seen` when
an auditable receipt is useful.

Critical broadcasts may require acknowledgement from the exact audience
snapshot. Those acknowledgements are explicit, batchable, and do not imply the
announced problem is fixed. A missed deadline creates one coordinator-facing
exception; it does not automatically open one issue per silent agent.
Unavailable agents are retired or reassigned through normal custody rules so a
dead identity cannot block the fleet indefinitely.

The deadline is an alert threshold, not a source of authority. Passing it may
cause a coordinator to investigate or publish an issue, but timestamp comparison
alone never acknowledges, retires, reassigns, or otherwise closes a lifecycle.

### 4.3 Corrections and storm control

Broadcasts are never deleted or rewritten. A correction publishes a new event
whose `supersedes` set names the obsolete announcement and explains the changed
fact. Queries display the current chain while retaining history.

The helper deduplicates by topic, affected interface, and explicit supersession;
enforces existing event-size bounds; and encourages one consolidated update
over repeated status messages. A derived topic index may accelerate queries but
is never authoritative.

Authority to publish is scoped:

- coordinators publish fleet lifecycle and known-main safety advisories;
- protocol owners publish changes to their protocol;
- interface owners publish compatibility changes to their exports; and
- the design steward publishes ratified normative changes.

Anyone may report an issue or friction. They do not gain authority to speak for
an interface merely by choosing its broadcast topic.

## 5. Required implementation and adversarial gates

The successor is not ready for activation until checked fixtures demonstrate:

1. two agents can continuously publish without either rebasing on the other;
2. a cached `inbox` or `tail` completes while another process holds a writer
   lock indefinitely;
3. concurrent transitions from one causal predecessor reduce to the documented
   lifecycle conflict;
4. a cross-agent reference outside the declared frontier is rejected;
5. an authority event with an incomplete active-agent frontier is rejected;
6. duplicate custody of one agent stream fails closed without force-push;
7. two host coordinators cannot both publish for one agent custody epoch;
8. cached reads and local candidate submission complete while the host
   coordinator is stalled on the network indefinitely;
9. a same-host dependent batch is either atomically visible with its complete
   closure or not remotely visible at all;
10. partial migration cannot admit events on both version-one and version-two
   substrates;
11. a friction report creates no target obligation and a promoted issue does;
12. audience resolution is exact and stable under later subscription changes;
13. informational broadcasts cause no mandatory acknowledgement events;
14. a required-ack broadcast handles retirement and reassignment without an
    immortal wait; and
15. cold replay and incremental replay produce exactly the same reduced state.

Performance fixtures should use enough concurrent writers and retained history
to expose asymptotic mistakes, but need not manufacture a fantastically large
event corpus. The acceptance claim is structural: unrelated publication has no
shared writable ref or global lock, and incremental work is proportional to
advanced streams.

## 6. Rejected alternatives

### Keep one branch and tune retry policy

Batching and exponential backoff can reduce push frequency, but every writer
still competes for one ref and long validation holds the same local lock. It
cannot establish the required non-contention property.

### Add one fleet-wide coordinator writer or merge queue

A single writer converts optimistic contention into an explicit bottleneck and
makes coordinator unavailability a fleet-wide outage. Coordinators should
not serialize facts from unrelated hosts. The host-local coordinators above are
sharded publishers: each owns only its local queues and the agent streams under
its current custody, so one unavailable host cannot stop another host.

### Commit a shared mutable index

An index branch merely moves the hot compare-and-swap point. Disposable local
indexes and caches are useful precisely because no publication depends on
updating them.

### Use one ref per event

This removes writer conflicts but grows the remote ref namespace with total
event count and makes discovery and retention unnecessarily expensive. One
linear ref per agent bounds ref count by fleet size while preserving independent
publication.

### Move coordination to issues, pull requests, or an external database

Those systems can provide excellent user interfaces, but they would cease to be
the Git-only, offline-replayable common substrate assumed by the project. They
may mirror authoritative events later; they are not the authority.

## 7. Questions for adversarial review

Review should particularly attack:

- whether sparse and complete frontiers preserve every version-one authority
  check without reintroducing a hot global ref;
- whether stream creation, identity custody, and migration fail closed under
  crashes and silent quota exhaustion;
- whether any read path still waits on a publication lock;
- whether friction stays cheap enough that agents report it, yet structured
  enough to synthesize;
- whether broadcast authority prevents both spoofing and centralization;
- whether audience snapshots and acknowledgement rules avoid silent misses
  without creating event storms; and
- whether Git hosting limits make one protected ref per active agent
  impractical before another layout is selected.

Until those questions are answered by review and fixtures, version one remains
the only normative coordination protocol.
