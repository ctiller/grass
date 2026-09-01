# Verified objects and modular linking

`VerifiedProgram (spec : SpecProcess resources)` remains the final exact
correctness gate. Large-system build locality is provided below that gate by
stable exported signatures and verified relocatable objects, not by weakening
the program index to an existential hidden specification.

## 1. Stable exported signatures

A subsystem exports only the facts its consumers may use:

```lean
structure ProgramSignature where
  calls : ExportedCallableFamily
  protocols : ExportedProcessProtocolFamily
  observations : ExportedObservationContract
  resources : ExportedSemanticResourceContract
  obligations : ExportedObligationTransfer
  providers : ProviderRequirementFamily
  abi : ExportedAbiFamily

structure ImplementsSignature
    (spec : SpecProcess resources) (sig : ProgramSignature) : Prop where
  behavior : ProjectedSpecContract spec = sig.observations
  calls : SpecExportsCallables spec sig.calls sig.abi
  protocols : SpecExportsProtocols spec sig.protocols
  resources : SpecEntailsExportedResourceContract spec sig.resources
  obligations : SpecTransfersExactly spec sig.obligations
  providers : SpecRequirementsEntail spec sig.providers
```

Private process state, topology, helper contracts, layouts, registers, buffer
sizes, and internal semantic components are absent. Changing them does not
invalidate a consumer when `ImplementsSignature` still proves the same value.

## 2. Verified relocatable object

```lean
structure VerifiedObject (sig : ProgramSignature) where
  privateResources : Type
  privateSpec : SpecProcess privateResources
  signature : ImplementsSignature privateSpec sig
  source : HierarchicalClosedAsmSource
  sections : RelocatableSectionFamily
  symbols : ObjectSymbolTable sig
  relocations : TypedRelocationFamily sections symbols
  machine : ObjectMachineCodeRefines privateSpec source sections
  writerRoundTrip : parseGobj (writeGobj this) = .ok this
```

The existential/private specification is lawful here because an object claims
only its exported interface. It is not lawful at the final product gate, where
the exact precious root specification is known and retained.

An object carries symbolic relocation targets, section alignment and
permissions, exported/imported ABI contracts, provider demands, resource and
obligation summaries, and a hierarchical machine certificate. Its proof does
not mention a final image base or offsets of unrelated objects.

## 3. Verified linker

```lean
structure LinkPlan (root : SpecProcess resources)
    (signatures : Array ProgramSignature) where
  composition : SignatureNetworkRefinesRoot signatures root
  providers : CoherentProviderSelection signatures
  layout : SectionLayoutPolicy
  exports : RootExportSelection root signatures

def linkVerified
    (plan : LinkPlan root signatures)
    (objects : HArray VerifiedObject signatures) :
    Except LinkError (VerifiedProgram root)
```

The linker checks exact symbol resolution, signature/ABI compatibility,
provider coherence, section permissions/alignment, relocation range and
encoding, import synthesis, resource/obligation composition, and entry/export
selection. Its connection theorem proves that parsing/loading the emitted image
produces the linked machine program assembled from those exact objects and that
the signature composition refines `root`.

Link failure is data, not unsoundness. Duplicate exports, unresolved symbols,
ABI mismatch, incompatible providers, overflowed relocations, permission
conflicts, or an unclosed root contract return a precise error.

## 4. Canonical source DAG and stable local proof identity

Large sources are canonical DAGs of shards, not one dependent vector copied
into every theorem type:

```lean
structure SourceShard where
  scopeId : StableScopeId
  publicSummary : MachineBoundarySummary
  imports : FiniteMap StableScopeId MachineBoundarySummary
  body : AuthoredAsmSource
  localIdentity : HashOfCanonicalSource body imports

structure SourceDag where
  shards : FiniteMap StableScopeId SourceShard
  edges : FiniteDependencyDag shards
  roots : FiniteSet StableScopeId
  importsExact : EveryImportMatchesOneExport shards edges

structure VerifiedShard (shard : SourceShard) where
  local : ShardSourceRefinesSummary shard.body shard.publicSummary
  dependencies : EveryLocalProofUsesOnly shard.imports
  sourceClosure : ExactLocalSymbolsReferencesAndExpansion shard
```

`StableScopeId` is a reviewed nominal identity. The cache key additionally uses
the canonical body and imported-summary hashes; it is not a proof. A local
certificate is indexed by the exact shard and small imported summaries, never
the entire program. The aggregate theorem folds `VerifiedShard` values over the
DAG and proves that recursive concatenation/linking is the exact root machine
source. Its root hash supports lookup and reproduction but cannot replace the
folded theorem.

Consequences:

- a body-only edit rechecks that shard and ancestors whose imported summary or
  layout actually changes;
- an implementation edit preserving an exported summary permits sibling and
  consumer proof reuse;
- an interface edit invalidates direct consumers and their affected ancestors;
- adding/removing an edge changes the finite dependency proof; and
- no local theorem elaborates or compares a tens-of-millions-instruction term.

Implementation acceptance measures clean work, one-instruction body edits,
interface edits, cache hits, proof bytes, and peak memory at one million and ten
million instructions. The design target is work proportional to the changed
shard plus affected ancestor/interface closure, with logarithmic or bounded
index lookup; no fixed numeric timing is claimed before measurement.

## 5. Invalidation and caching

Object proofs are opaque module exports and may be cached by source/theorem/
profile hashes. A private edit rechecks its changed fragments, ancestor closure
nodes, and object proof. Consumers need not re-elaborate when the signature hash
and theorem environment are unchanged. Relinking necessarily revisits affected
symbol/layout/relocation ancestors; Grass makes no false constant-time claim.

Final PE/ELF bytes can change globally when layout changes, but instruction
semantics do not. The linker re-proves the cheap layout/relocation connection
from unchanged object certificates instead of replaying every instruction
proof. Build reports measure actual elaboration, kernel, cache, and link work.

## 6. Serialized `.gobj`

`.gobj` is an optional deterministic serialization of the relocatable object
payload and certificate references. It obeys the corpus laws:

- `parseGobj (writeGobj object) = .ok object`;
- every successful parse satisfies the binary grammar and structural
  invariants; and
- corrupt, stale-environment, or unknown-checker certificates are rejected.

A standalone linker may consume `.gobj` only through a small verified checker
whose accepted certificate theorem is connected back to Lean kernel theorems.
The format and checker do not become a second unverified emission route.

## 7. Acceptance fixtures

The object model is retained only if fixtures demonstrate:

- changing a private instruction without changing an export avoids consumer
  elaboration and reuses sibling fragment proofs;
- changing an ABI/resource/obligation export invalidates exactly its consumers;
- moving an object rechecks relocation/layout connection but not machine
  semantics;
- a cross-object call, process channel, and SPIR-V embedding compose to one root;
- every malformed symbol, relocation, provider, permission, and certificate
  mutation is rejected; and
- clean and incremental measurements at increasing object counts remain within
  the explicit proof-economy budgets.
