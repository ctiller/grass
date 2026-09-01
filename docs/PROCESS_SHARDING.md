# Process sharding and incremental composition

Status: normative design. Implementation evidence is governed by
[IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md).

Grass verifies one root `SpecProcess`, but it must not represent a large
realization as one closed process sum, one global cancellation table, or one
proof indexed by the complete process plan. Those shapes make a local process
edit change downstream theorem types and defeat `.olean` locality before the
machine layer is reached.

This document applies the certificate-DAG discipline from
[OLEAN_SHARDING.md](OLEAN_SHARDING.md) to process specifications,
realizations, and blends.

## 1. The unit of process separate compilation

A process shard is normally a service, protocol role, actor family, subsystem,
or bounded mutually recursive group. It publishes a small signature and hides
its topology and proofs.

```lean
structure ProcessSignature where
  id : StableProcessSignatureId
  requests : InterfaceFamily
  responses : DependentResponseFamily requests
  events : InterfaceFamily
  observations : ObservationBoundary
  behavior : ProcessTraceContract requests responses events observations
  specFragment : StableSpecFragmentId
  behaviorDenotesFragment : behavior.Denotes specFragment
  resources : ResourceBoundarySummary
  obligations : ObligationBoundarySummary
  progress : ProgressBoundarySummary
  cancellation : CancellationBoundarySummary
  providers : ProviderDemandSummary

structure ProcessShardCertificate (sig : ProcessSignature) where
  private State : Type
  private topology : OpenProcessGraph State
  private realization : ProcessRealization topology
  private localProof : LocalProcessCorrect realization
  public boundary : RealizesProcessSignature realization sig
```

The public theorem type contains `sig`, including its semantic `behavior`, but
not `topology`, `State`, a global registry, or the source of child processes. A
body edit with the same behavioral and operational boundary rebuilds the shard
certificate but does not alter its consumers.

`ProcessTraceContract` is an abstract input/event/result/observation trace
relation, not merely an interface shape. The certificate's public theorem means:

```lean
def RealizesProcessSignature
    (realization : ProcessRealization topology)
    (sig : ProcessSignature) : Prop :=
  ∀ execution, realization.Accepts execution →
    sig.behavior.Accepts
      (sig.observations.project (execution.boundaryTrace sig))
```

Two processes with the same channel types but different permitted behavior do
not have the same signature. `specFragment` is a stable nominal reference used
for dependency and requirement-key routing; `behaviorDenotesFragment` carries
the actual proposition and prevents that identifier from becoming a hash-based
semantic shortcut.

`StableProcessSignatureId` is a reviewed nominal identity plus interface
version. Content hashes are cache keys only. A changed semantic boundary must
receive a changed interface version; an unchanged boundary may retain its
identity after the replacement proof checks.

## 2. Open registries, never a master process sum

Each module owns only its local role keys:

```lean
structure ProcessRegistryFragment where
  namespace : StableScopeId
  entries : Array ProcessRegistryEntry
  unique : PairwiseDistinct entries.key

def ProcessRegistryFragment.merge
    (left right : ProcessRegistryFragment)
    (separate : NamespacesDisjoint left right) :
    ProcessRegistryFragment
```

A large program does not declare `inductive WholeProgramProcessKind`. Registry
merge preserves the nominal identity of every unaffected entry. Generated
lookup tables, dispatch ordinals, erasure maps, source maps, and diagnostic
names are artifact views of the merged fragments; they are not public proof
indexes.

Generative families such as HTTP/2 connections and streams export a family
key and an instance-generation discipline. They do not enumerate runtime
instances or add constructors to a whole-program sum.

## 3. Facet-indexed local proofs

A composition invariant depends on the smallest named facet that supplies its
facts:

```lean
structure ProcessFacetSummary where
  channels : ChannelSummary
  sharedState : SharedStateSummary
  spawn : SpawnSummary
  cancellation : ScopedCancellationSummary
  resources : ResourceBoundarySummary
  obligations : ObligationBoundarySummary
  progress : ProgressBoundarySummary

structure FacetCertificate (facet : ProcessFacetSummary) where
  private implementation : ProcessFacetImplementation
  valid : implementation.Satisfies facet
```

The HTTP/2 flow-credit proof is indexed by the connection/stream channel and
resource facets. It is not indexed by the listener topology, worker count,
Win32 polling choice, route body, or complete `serverProcessPlan`. A graphics
ownership proof is similarly independent of the storage realization with
which it is later blended.

The elaborator derives mechanical records that merely rename already proved
facet lemmas. An author supplies novel coupling invariants and selects which
facets they consume. Adding a new facet cannot silently enlarge an existing
proof's dependency set.

## 4. Scoped cancellation

Cancellation coverage is proved per shard or lexical process scope:

```lean
structure ScopedCancellationCertificate
    (scope : ProcessScopeSummary) where
  policy : CancellationPolicy scope.publicCancellationPoints
  callsExact : policy.calls = scope.blockingCalls
  localSafe : EveryCancellationRouteSafe scope policy

def ScopedCancellationCertificate.compose
    (left : ScopedCancellationCertificate a)
    (right : ScopedCancellationCertificate b)
    (wiring : CancellationBoundaryCompatible a b) :
    ScopedCancellationCertificate (a.compose b wiring)
```

`callsExact` compares only the calls discovered in that scope. An added
blocking call rebuilds its local certificate and the bounded aggregate path.
It does not change a million-entry global key-set equality. Cross-boundary
cancellation is an explicit exported endpoint; internal cancellation points
remain private.

The algebraic form
`uncancellable |> cancelpoint |> uncancellable` is summarized at the shard
boundary. Composition may preserve, restrict, or expose cancellation according
to the typed boundary theorem; it never rediscovers the child CFG.

## 5. Resource and obligation summaries

The resource model is a parameter of the precious behavior specification. A
process shard exports parametric resource transfer and optional selected bounds:

```lean
structure ResourceBoundarySummary where
  axes : ResourceAxisFamily
  requires : ResourceVector axes
  peakDelta : ResourceVector axes
  returns : ResourceVector axes
  backpressure : BackpressureBoundary axes

structure ObligationBoundarySummary where
  accepts : ObligationFamily
  emits : ObligationFamily
  discharges : ObligationFamily
  terminalDisposition : Outcome → ObligationDisposition
```

Axes may include bytes, allocation count, file descriptors, sockets, handles,
GPU objects, queue credit, or application-defined resources. Composition folds
these summaries using the selected resource algebra. The child proof remains
valid when a different deployment profile supplies a different admissible
bound. Only a consumer of the changed selected bound rebuilds.

A theorem such as “each admitted web request uses at most `N` bytes and two
stream slots” is local to the request shard plus its channel boundary. Global
backpressure follows from bounded channel capacity and aggregate resource laws;
it does not unfold every request process.

## 6. Composition and balanced aggregates

Composition consumes signatures and facet certificates:

```lean
def composeProcessShards
    (left : ProcessShardCertificate a)
    (right : ProcessShardCertificate b)
    (wiring : ProcessBoundaryWiring a b)
    (law : WiringRealizesContracts
      a.behavior b.behavior wiring (ProcessSignature.compose a b wiring).behavior) :
    ProcessShardCertificate (ProcessSignature.compose a b wiring)
```

The implementation stores children existentially behind their checked
boundaries. The public result mentions only the composed signature. Generated
aggregate modules have bounded fanout and form a balanced DAG, just like
verified machine objects.

For an acyclic graph, composition follows the dependency DAG. Mutually
recursive process groups are condensed into a strongly connected component.
The SCC owns one local coinductive invariant/progress certificate and exports
one summary; callers do not depend on its internal cycle. Changing a member
rechecks the SCC, not unrelated SCCs.

Some clean builds remain at least linear in compact summary count: namespace
uniqueness, boundary closure, provider coherence, root reachability, and final
requirement coverage. These checks fold manifests and summaries. They do not
re-elaborate child state machines or proofs.

The final aggregate closes the behavioral path to the precious root:

```lean
structure RootProcessCertificate {R : Type} (root : SpecProcess R) where
  signature : ProcessSignature
  aggregate : ProcessShardCertificate signature
  requirementOrigins : EveryContractClauseHasRootOrigin signature.behavior root
  rootRefinement : signature.behavior.Refines root.behavior
  observationExact : signature.observations.Refines root.observationFilter
```

`VerifiedProgram root` consumes this root certificate. Replacement under an
unchanged signature is sound because the signature retains the same behavioral
relation, not merely because its messages and resource summaries still line up.

## 7. Staged blending and heterogeneous lowering

A blended graph may contain abstract and lowered shards simultaneously:

```text
GraphicsSpec  x  StorageSpec  x  SimulationSpec
      |
VulkanShard   x  StorageSpec  x  SimulationSpec
      |
VulkanShard   x  IOCPShard    x  SimulationSpec
      |
VulkanShard   x  IOCPShard    x  X86SimulationShard
```

Replacing one shard requires a refinement theorem with the same semantic
process signature. The blend certificate for unaffected siblings is reused. Provider
coherence is checked from compact provider summaries at aggregates and the
root, preventing incompatible global selections such as Metal and Vulkan for
one graphics contract.

Serial lowering is a standard shard realization. The flattening theorem turns
a serializable process graph into one sequential process while preserving the
chosen observation filter, resources, obligations, and progress assumptions.
It may then be lowered again fractally. The theorem is applied to summaries and
local commutation certificates, not by comparing two globally flattened traces.

## 8. File and import shape

The normative large-component shape is:

```text
Component/ProcessSig.lean   process signature and public protocols
Component/ProcessImpl.lean  private state, local graph, invariants, realization
Component/ProcessCert.lean  opaque boundary and facet certificates
Component/MachineSig.lean   callable/basic-block/ABI signature
Component/MachineImpl.lean  assembly or shader source
Component/MachineCert.lean  opaque VerifiedObject
```

Small programs may colocate these declarations. The import graph must still
obey the same boundary: consumers import `ProcessSig` or an opaque certificate,
never `ProcessImpl`. Generated aggregate modules import only child certificate
modules. A convenient single author file may be split into these Lake facets by
a checked generator, provided the generated boundaries and imports are
inspectable.

Precious behavior specifications may also be split by independently changing
requirement families. Leaf process certificates import only the spec-fragment
summaries they discharge. One application root composes those fragments into
the single `SpecProcess` indexing `VerifiedProgram`.

## 9. Required locality mutations

Implementation acceptance adds the following process mutations to the common
ratchet:

| Mutation | May rebuild | Must remain cached |
|---|---|---|
| private process-state or step edit, same boundary | local impl/cert and aggregate path | sibling shards and callers of unchanged signature |
| local invariant edit | consuming facet cert, shard cert, aggregate path | unrelated facets and machine shards |
| add an internal cancellation point | local cancellation cert and aggregate path | cancellation certs in other scopes |
| add an exported channel | changed signature, direct consumers, aggregate path | unrelated subtrees |
| change worker count within same semantic resource contract | selected realization/resource facet | precious behavior and unrelated machine shards |
| lower one abstract subsystem | replacement shard and blend aggregate path | other abstract or lowered subsystems |
| change one precious requirement key | its fragment and certificates consuming that key | unrelated requirement fragments and realizations |

Reports record re-elaborated modules, imported public/private modules, changed
certificate identities, residual goals, aggregate nodes, wall time, peak memory,
and cache hits. Acceptance is structural first: a private leaf edit that causes
all process modules or all machine certificates to rebuild fails even if the
wall time happens to be small.

## 10. Forbidden scalable-looking shortcuts

The following fail design or implementation review:

- a closed whole-program `ProcessKind`, `ProtocolKey`, or role sum;
- one registry value imported by every process module;
- a composition witness indexed by the complete realization plan when each
  field consumes only a facet;
- global cancellation validity defined by equality with all blocking calls;
- theorem types containing the full process graph or state machine;
- a process signature containing channel/resource shape but no public trace
  relation tied to a precious specification fragment;
- aggregate tactics that rediscover child invariants or unfold private proofs;
- resource bounds baked into an algorithm theorem when the theorem can remain
  parametric;
- flattening every process trace to prove local commutation; or
- using a digest or generated manifest as proof of a process boundary.

These are foundational failures, not optimization opportunities. If Lean/Lake
cannot preserve the specified opacity and import locality, Grass changes the
process/certificate factoring before growing the concurrency or platform
library.
