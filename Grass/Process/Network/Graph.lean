import Grass.Process.Network.Exposure
import Grass.Process.Protocol.Registry

/-!
# The process graph: which processes exist, and over what state

`docs/PROCESS.md` §3 opens with the question this module answers:

> The primary modelling question is: **which processes exist, and over what
> logical state do they act?** The answer is a reviewed replaceable construction
> input, not automatically part of the precious specification.

Everything here is therefore *disposable*. `docs/FOUNDATION.md` law 15 makes the
root `SpecProcess` the only precious thing and says explicitly that "no selected
role decomposition, process population, state partition, channel weave,
scheduler, or physical topology" is. A different graph may realize the same
root, and this module's job is to make that substitution a theorem rather than a
rewrite.

## What is deliberately not here

Channels. `docs/PROCESS.md` §3 splits `ProcessGraph` from `ProcessTopology` for
a stated reason:

> `ProcessGraph` exists separately so topology and channel contracts can
> quantify over the endpoint protocols, spawn/population laws, shared-state
> interference, and process-network assertions without a self-referential
> structure declaration.

So a `ChannelContract` may mention a graph, and the completed plan adds the
edges. Putting them in one record would make the contract's type mention the
contract.

## Shared state is named, not inferred

§3: "Nothing is shared merely because two transitions mention the same Lean
value." `SharedRegion` is an explicit index, `sharedAccess` is an explicit
capability per role, and a region no role may write is provably immutable —
which is what lets an immutable route table be charged once by a resource metric
instead of per reader.

The *interference invariant* over a shared region is not here. It is a
`WeaveInvariantMixin` and is M4 work; what this module fixes is the capability
declaration those invariants are framed against.
-/

namespace Grass.Process

universe u w v r

/--
What a role may do to a shared region.

Three independent capabilities rather than a linear order, because "may write
only through atomic operations" is not between "may read" and "may write": it is
a different discipline, and collapsing it would make an atomic counter
indistinguishable from a plain one.
-/
structure LogicalAccess where
  /-- The role may observe the region. -/
  mayRead : Bool
  /-- The role may change the region. -/
  mayWrite : Bool
  /-- Every access is through an atomic operation. -/
  atomic : Bool
  deriving DecidableEq, Repr

namespace LogicalAccess

/-- No access at all. The region is invisible to this role. -/
def none : LogicalAccess := ⟨false, false, false⟩

/-- Read-only. -/
def readOnly : LogicalAccess := ⟨true, false, false⟩

/-- Ordinary read and write. -/
def readWrite : LogicalAccess := ⟨true, true, false⟩

/-- Read and write, but only through atomic operations. -/
def atomicReadWrite : LogicalAccess := ⟨true, true, true⟩

/-- The role touches the region at all. -/
def Touches (access : LogicalAccess) : Prop :=
  access.mayRead = true ∨ access.mayWrite = true

/--
Two roles' accesses to the same region race if both touch it, at least one
writes, and they are not both atomic.

This is the syntactic obligation, not the proof. A plan whose `sharedAccess`
declares a conflicting pair owes an interference invariant or a proof that the
two roles are never concurrently live; a plan with no conflicting pair owes
neither. `docs/MEMORY_MODEL.md` owns what a *physical* race is, and the
representation relation connects them; this is the logical-ownership graph
`docs/PROCESS.md` §3 says the memory realization later maps.
-/
def Conflicts (left right : LogicalAccess) : Prop :=
  left.Touches ∧ right.Touches ∧
    (left.mayWrite = true ∨ right.mayWrite = true) ∧
    ¬ (left.atomic = true ∧ right.atomic = true)

@[simp] theorem not_touches_none : ¬ none.Touches := by
  simp [Touches, none]

/-- A role with no access conflicts with nothing. -/
@[simp] theorem not_conflicts_none_left (access : LogicalAccess) :
    ¬ none.Conflicts access := by
  simp [Conflicts, Touches, none]

/-- Readers never conflict with readers. -/
theorem readOnly_not_conflicts_readOnly : ¬ readOnly.Conflicts readOnly := by
  simp [Conflicts, Touches, readOnly]

/-- A writer conflicts with a reader. -/
theorem readWrite_conflicts_readOnly : readWrite.Conflicts readOnly := by
  simp [Conflicts, Touches, readWrite, readOnly]

/-- Two atomic users do not conflict; their discipline is the mediation. -/
theorem atomic_not_conflicts_atomic :
    ¬ atomicReadWrite.Conflicts atomicReadWrite := by
  simp [Conflicts, Touches, atomicReadWrite]

end LogicalAccess

/--
How many instances of a role may be live at once.

`docs/PROCESS.md` §3 names the three cases: "one root and one child call at a
time", "four supervised worker instances", "one request process per accepted
connection up to a resource policy".
-/
inductive PopulationBound
  /-- Exactly one, for the whole execution. -/
  | exactlyOne
  /-- At most this many live at once. -/
  | atMost (limit : Nat)
  /--
  Generative: a new instance per admitted event, bounded only by the selected
  resource policy.

  This constructor is a *debt*, and it is spelled to be conspicuous. The bound
  exists — `docs/FOUNDATION.md` law 20 requires dynamic population to be bounded
  — but it lives in the resource certificate, which `Grass.Resource` owns and
  which `Grass.Process.Resource` instantiates. A plan that uses this constructor
  and never produces that certificate has an unbounded population, and the
  reviewer's job is to look for exactly this constructor.
  -/
  | boundedByResourcePolicy
  deriving DecidableEq, Repr

/--
Whether a role's instances need a generation.

`docs/FOUNDATION.md` law 22 applies to any identity that can be recycled. A
statically identified singleton — the root, a fixed worker slot that is never
replaced — has one identity for the whole execution and needs no generation. A
role whose instances die and are replaced does, or a stale completion carrying
the old numeric identity would be accepted by the new incarnation.
-/
inductive InstanceIdentity
  /-- One identity for the whole execution; no incarnation can be replaced. -/
  | static
  /-- Each incarnation gets a fresh generation over the monotone history. -/
  | generational
  deriving DecidableEq, Repr

/-- The population discipline of every role in a graph. -/
structure PopulationLaw (ProcessKind : Type r) where
  /-- How many of this role may be live. -/
  bound : ProcessKind → PopulationBound
  /-- Whether this role's instances carry generations. -/
  identity : ProcessKind → InstanceIdentity

namespace PopulationLaw

variable {ProcessKind : Type r}

/-- The roles whose bound is deferred to a resource certificate. -/
def DeferredToResources (law : PopulationLaw ProcessKind)
    (kind : ProcessKind) : Prop :=
  law.bound kind = .boundedByResourcePolicy

/--
A role that can be replaced needs a generation.

Not derivable — `bound` says how many may be live, not whether one may die and
be replaced — so it is an obligation a plan discharges. It is stated here so a
plan that declares `exactlyOne` with `static` for a *restartable* supervised
child is rejected at the graph rather than at the driver.
-/
def ReplaceableRolesAreGenerational (law : PopulationLaw ProcessKind)
    (Replaceable : ProcessKind → Prop) : Prop :=
  ∀ kind, Replaceable kind → law.identity kind = .generational

/-- A singleton static role. The root's normal declaration. -/
def singletonStatic : PopulationBound × InstanceIdentity := (.exactlyOne, .static)

end PopulationLaw

/--
The roles of a realization, the state they share, and who may spawn whom.

Channels are absent by design; see the module note.
-/
structure ProcessGraph (registry : ProtocolRegistry.{u, w, v})
    (boundary : DriverBoundary.{u}) where
  /-- The roles. Not a whole-program sum: see `docs/PROCESS_SHARDING.md` §2. -/
  ProcessKind : Type r
  /-- The named regions of shared logical state. -/
  SharedRegion : Type r
  /-- What each region holds. -/
  SharedState : SharedRegion → Type w
  /-- Which protocol each role speaks. -/
  protocolKey : ProcessKind → registry.Key
  /-- The role that faces the driver. -/
  root : ProcessKind
  /-- The root's protocol exposes the driver boundary. -/
  rootBoundary :
    ProtocolExposesBoundary (registry.protocol (protocolKey root)) boundary
  /--
  Which roles may create which.

  A relation, not a tree: `docs/PROCESS.md` §3 lets a connection role spawn both
  a stream role and a decoder role, and lets several roles spawn API children.
  Parenthood of a particular *instance* is a topology fact, not a graph fact.
  -/
  maySpawn : ProcessKind → ProcessKind → Prop
  /-- What each role may do to each shared region. -/
  sharedAccess : ProcessKind → SharedRegion → LogicalAccess
  /-- How many instances of each role, and whether they carry generations. -/
  population : PopulationLaw ProcessKind

namespace ProcessGraph

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  (graph : ProcessGraph.{u, w, v, r} registry boundary)

/-- The protocol a role speaks. -/
def protocol (kind : graph.ProcessKind) : ProcessSpec.{u, w} :=
  registry.protocol (graph.protocolKey kind)

/--
Two roles conflict over a region when their declared accesses race.

The pairs a plan owes an interference invariant or a mutual-exclusion proof for.
-/
def Conflicting (left right : graph.ProcessKind)
    (region : graph.SharedRegion) : Prop :=
  (graph.sharedAccess left region).Conflicts (graph.sharedAccess right region)

/--
A region no role may write.

`docs/PROCESS.md` §5: "Shared read-only storage is counted once". That resource
law needs this predicate to be a fact about the graph and not a comment, which
is why `sharedAccess` is total and explicit rather than a partial map with an
implicit default.
-/
def Immutable (region : graph.SharedRegion) : Prop :=
  ∀ kind, (graph.sharedAccess kind region).mayWrite = false

/-- No pair of roles conflicts over an immutable region. -/
theorem immutable_no_conflict {region : graph.SharedRegion}
    (immutable : graph.Immutable region) (left right : graph.ProcessKind) :
    ¬ graph.Conflicting left right region := by
  intro conflict
  rcases conflict.2.2.1 with writes | writes
  · exact absurd writes (by simp [immutable left])
  · exact absurd writes (by simp [immutable right])

/--
The roles reachable from the root by spawning.

A role no chain of `maySpawn` reaches from the root is dead weight in the plan:
no instance of it can ever exist. A plan is expected to prove `root`-reachability
of every role it declares, which is the graph-level half of
`docs/PROCESS_SHARDING.md` §6's "root reachability" fold.
-/
inductive SpawnReachable (graph : ProcessGraph.{u, w, v, r} registry boundary) :
    graph.ProcessKind → Prop
  | root : SpawnReachable graph graph.root
  | spawned {parent child : graph.ProcessKind}
      (reachable : SpawnReachable graph parent)
      (authority : graph.maySpawn parent child) : SpawnReachable graph child

/-- Every declared role can actually occur. -/
def NoDeadRoles : Prop := ∀ kind, graph.SpawnReachable kind

/--
The root exposes the boundary and is reachable from itself, so a graph with no
dead roles has a root-reachable role for every protocol it names.

Trivial, and stated because it is what an aggregate's reachability fold consumes:
the fold should apply an exported theorem, not re-derive the base case.
-/
theorem root_reachable : graph.SpawnReachable graph.root := .root

end ProcessGraph

end Grass.Process
