import Grass.Process.Network.Graph
import Grass.Process.Nominal
import Grass.Specification.Boundary

/-!
# Topology: instances, generations, channel sessions, and message occurrences

`docs/PROCESS.md` §3 adds to the graph the things that have *identity*: which
incarnation of which role, which session of which channel, and which message on
which session.

Every identity here is nominal and every one of them is subject to
`docs/FOUNDATION.md` law 22:

> process generations, channel epochs, child/message occurrences, and
> replacements are fresh over a monotone execution history; stale completions
> never regain authority after numeric reuse.

`Grass/Process/Nominal.lean` proves what a monotone history guarantees. This
module is where the four kinds of identity law 22 names are actually built, and
each carries its `NominalKind` so that a recycled carrier value in a different
role is a different identity by construction rather than by convention.

## Product identity and scheduling identity are different fields

`docs/PROCESS.md` §2 draws a line this module has to keep:

> Product-visible request identity may be a field of `Demand`; scheduling and
> correlation identities remain realization-private.

So a `ProcessRef` has two parts. `instanceId` is the product-visible identity of
the thing — an HTTP/2 connection number, a worker slot — and it is the part a
specification is allowed to mention. `generation` is the incarnation, and it is
realization-private: it exists so a stale completion addressed to the previous
incarnation of connection 7 fails a check, and no precious specification may
depend on it.

## What is not here

An earlier version of this module gave `ProcessTopologyCore` an `edgeRolesRelated`
field requiring every channel edge's endpoints to be spawn-adjacent or to share
a spawner. `docs/PROCESS.md` §3 declares no such field, and it was wrong on its
own terms: nothing spawns the root, so it rejected every edge between the root
and a role that is not its direct child, and it rejected cousin edges outright.
A shutdown channel from a listener to a stream is an ordinary topology.

Channel connectivity is a plan-level obligation — an edge no execution can use
is dead weight, and that is checked where the population and the channel
contracts are, not as a well-formedness condition on the topology.

## Why this is `ProcessTopologyCore` and not `ProcessTopology`

`docs/PROCESS.md` §3 declares `ProcessTopology` with three law fields: spawn,
cancellation, and supervision. This structure carries only spawn, and it is
named `ProcessTopologyCore` for exactly that reason.

`agent-bus` disposition `g-design:5`, ruling on issue `c-process:10`:

> Ratify cancellation and supervision as optional topology facets so simple
> processes pay no ceremony. Rename the weaker exported structure
> `ProcessTopologyCore`; reserve `ProcessTopology` for the aggregate carrying
> every facet required by the selected specification, with named composition
> theorems recovering cancellation and supervision contracts.

An earlier version of this module exported the weaker record *as*
`ProcessTopology`, and `g-reviewer` was right to block on it: a downstream
consumer could hold a value of that name while assuming the lifecycle authority
its type does not contain. The name is now reserved for the aggregate, which
lands with the facets in M3; nothing may claim it until then.

The reason is `docs/PROCESS_SHARDING.md` §3 and §10, which require a composition
invariant to depend "on the smallest named facet that supplies its facts" and
list as a foundational failure "a composition witness indexed by the complete
realization plan when each field consumes only a facet". A channel contract
consumes the endpoints and the spawn law; it does not consume the restart
intensity window. Putting all three in one record would make every channel proof
depend on the supervision policy, and adding a cancellation point would rebuild
proofs that cannot mention one.

Cancellation and supervision are therefore separate certificates over a
topology, landing with the rest of M3. `docs/PROCESS_IMPLEMENTATION_PLAN.md`
§10.8 records the deviation.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r

/--
A graph plus the things that have identity: instances, the edges between roles,
and the authority to create an instance.

Extends `ProcessGraph`, so a topology is a graph and the substitution of one
topology for another is still a substitution of graphs.
-/
structure ProcessTopologyCore (registry : ProtocolRegistry.{u, w, v})
    (boundary : DriverBoundary.{u})
    extends ProcessGraph.{u, w, v, r} registry boundary where
  /--
  The carrier of nominal identities.

  A parameter, not a fixed type: the mechanism that makes carriers unrepeatable
  is a supply with a private constructor, and that belongs to `Grass.Core`. What
  this module needs of it is only decidable equality, so that a generation check
  is a decision and not a proof obligation at every dispatch.
  -/
  Carrier : Type r
  /-- Carriers are comparable. -/
  carrierDecidableEq : DecidableEq Carrier
  /--
  The product-visible identity of an instance of a role.

  This is the part a specification may mention: a connection number, a stream
  identifier, a worker slot. `Unit` for a singleton role.
  -/
  InstanceId : ProcessKind → Type r
  /-- The communication edges. -/
  ChannelKind : Type r
  /-- The sending and receiving roles of each edge. -/
  endpoints : ChannelKind → ProcessKind × ProcessKind
  /--
  Which roles may create which *instances*, refining the graph's role-level
  authority.

  `maySpawn` says a connection role may create stream roles. This says which
  stream instances a *given* connection instance may create, which is what stops
  connection 3 from spawning a stream belonging to connection 5.
  -/
  spawnAuthority : ∀ parent child : ProcessKind,
    maySpawn parent child → InstanceId parent → InstanceId child → Prop

namespace ProcessTopologyCore

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  (topology : ProcessTopologyCore.{u, w, v, r} registry boundary)

instance : DecidableEq topology.Carrier := topology.carrierDecidableEq

/--
A reference to one incarnation of one instance of one role.

See the module note for why `instanceId` and `generation` are separate fields.
-/
structure ProcessRef (kind : topology.ProcessKind) where
  /-- The product-visible identity. A specification may mention this. -/
  instanceId : topology.InstanceId kind
  /-- The incarnation. Realization-private; a stale message fails on this. -/
  generation : LogicalNominal topology.Carrier
  /-- The generation is a process generation and not some other identity. -/
  isGeneration : generation.kind = .processGeneration

/--
A channel session: an edge, its two endpoint incarnations, and an epoch.

`docs/PROCESS.md` §3 requires all four. Dropping the epoch and identifying a
session by its endpoints would let a closed-and-reopened channel inherit the old
session's in-flight messages.
-/
structure ChannelId (edge : topology.ChannelKind) where
  /-- The sending incarnation. -/
  sender : topology.ProcessRef (topology.endpoints edge).1
  /-- The receiving incarnation. -/
  receiver : topology.ProcessRef (topology.endpoints edge).2
  /-- This session of this edge between these two incarnations. -/
  epoch : LogicalNominal topology.Carrier
  /-- The epoch is a channel epoch and not some other identity. -/
  isEpoch : epoch.kind = .channelEpoch

/--
One message on one session.

`channel` and `message` are phantom indices: they appear in the type and in no
field. That is what they are for. An occurrence of a `Settings` frame on
connection 3's writer session has a *different type* from one on connection 5's,
so a routing proof cannot mix them up and a resolution cannot be applied to the
wrong channel. What makes two sends of an *equal* payload on the *same* session
two occurrences is the `id` field, not the indices.

The affine resolve token that makes an occurrence consumable exactly once is
deliberately not a field here. `docs/PROCESS.md` §3 is explicit: "The
`MessageOccurrence` carries only its nominal identity; the unique affine
`ResolveToken occurrence.id` is an owned assertion inside `Escrow`, not a field
whose Lean value is assumed noncopyable." A Lean record field is copyable, so a
field claiming affinity would claim something the type system does not enforce.
-/
structure MessageOccurrence {edge : topology.ChannelKind}
    (channel : topology.ChannelId edge) {Message : Type w} (message : Message) where
  /-- The occurrence's identity. -/
  id : LogicalNominal topology.Carrier
  /-- It is a message occurrence and not some other identity. -/
  isMessage : id.kind = .messageOccurrence

/--
An occurrence together with the session it is on.

`docs/PROCESS.md` §3's `ChannelOccurrence`. `ChannelContract` quantifies over
occurrences of an *edge* without having chosen a session, so the session has to
travel with the occurrence rather than be a separate parameter: a contract that
took `channel` and `occurrence` apart could be instantiated with an occurrence
from one session and a session index from another, and nothing in the types
would object.
-/
abbrev ChannelOccurrence (edge : topology.ChannelKind) {Message : Type w}
    (message : Message) : Type r :=
  Sigma fun channel : topology.ChannelId edge =>
    topology.MessageOccurrence channel message

namespace ProcessRef

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
  {kind : topology.ProcessKind}

/--
Two references to the same role are the same incarnation when their generations
agree.

The check a driver performs on every delivery. It is stated for the *same* role
because references to different roles have different types, which is itself part
of the discipline: a completion for a worker cannot be delivered to a connection
even if the numbers coincide.
-/
def SameIncarnation (left right : topology.ProcessRef kind) : Prop :=
  left.generation = right.generation

/--
A stale reference: one addressed to an incarnation that is no longer the live
one.

This is the shape of the check `docs/PROCESS.md` §3 requires of a driver — "a
driver proof that stale physical events fail the generation/session check" — and
`NominalHistory.never_fresh_again` is why it can be trusted: a generation in the
history is never fresh again, so a new incarnation provably has a different one.
-/
def Stale (reference current : topology.ProcessRef kind) : Prop :=
  ¬ reference.SameIncarnation current

/--
Distinct generations make a reference stale, whatever the instance identity.

The property a numeric-slot-reusing driver relies on: reusing instance number 7
is safe precisely because the generation differs.
-/
theorem stale_of_generation_ne {reference current : topology.ProcessRef kind}
    (different : reference.generation ≠ current.generation) :
    reference.Stale current := different

/--
The reference names a generation this execution actually allocated.

A driver's dispatch check has two halves: the generation is in the history (it
was really allocated) and it equals the live one (it is not stale). The first
stops a fabricated reference; the second stops a stale one.
`docs/PROCESS.md` §3 requires both, and a check that omitted the first would
accept an identity no transition ever created.
-/
def Allocated (reference : topology.ProcessRef kind)
    (history : NominalHistory topology.Carrier) : Prop :=
  reference.generation ∈ history.used

/--
A reference cannot be both allocated and fresh.

The disjointness that makes the two halves of the dispatch check independent: an
allocated reference is by definition not one a spawn transition could be handing
out now.
-/
theorem not_fresh_of_allocated {reference : topology.ProcessRef kind}
    {history : NominalHistory topology.Carrier}
    (allocated : reference.Allocated history) :
    ¬ history.Fresh reference.generation :=
  fun fresh => fresh allocated

end ProcessRef

section KindTags

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}

/--
A message occurrence's identity is never a process generation.

Immediate from the `NominalKind` tags, and worth stating because the alternative
— identities distinguished only by which field they were stored in — is exactly
the confusion that lets a stale completion be accepted by a different subsystem.
-/
theorem occurrence_kind_distinct {edge : topology.ChannelKind}
    {channel : topology.ChannelId edge} {Message : Type w} {message : Message}
    (occurrence : topology.MessageOccurrence channel message)
    {kind : topology.ProcessKind} (reference : topology.ProcessRef kind) :
    occurrence.id ≠ reference.generation := by
  intro equal
  have tags : NominalKind.messageOccurrence = NominalKind.processGeneration := by
    rw [← occurrence.isMessage, ← reference.isGeneration, equal]
  exact absurd tags (by decide)

/-- A channel epoch is never a process generation, for the same reason. -/
theorem epoch_kind_distinct {edge : topology.ChannelKind}
    (channel : topology.ChannelId edge) {kind : topology.ProcessKind}
    (reference : topology.ProcessRef kind) :
    channel.epoch ≠ reference.generation := by
  intro equal
  have tags : NominalKind.channelEpoch = NominalKind.processGeneration := by
    rw [← channel.isEpoch, ← reference.isGeneration, equal]
  exact absurd tags (by decide)

end KindTags

end ProcessTopologyCore

end Grass.Process
