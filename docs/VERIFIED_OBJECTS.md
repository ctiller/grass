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
structure GobjPayload where
  formatVersion : GobjFormatVersion
  scope : StableScopeId
  sections : SerializableRelocatableSections
  symbols : SerializableObjectSymbols
  relocations : SerializableTypedRelocations sections symbols
  imports : SerializableImportManifest
  sourceMap : SerializableSourceMap

structure VerifiedObject (sig : ProgramSignature) where
  privateResources : Type
  privateSpec : SpecProcess privateResources
  signature : ImplementsSignature privateSpec sig
  source : HierarchicalClosedAsmSource
  payload : GobjPayload
  payloadSourceExact : PayloadEncodesExactSource payload source
  payloadExports : PayloadExportsSignature payload sig
  payloadImports : PayloadImportsSignature payload sig
  machine : ObjectMachineCodeRefines privateSpec source payload
```

Each serialized section also declares how relocations at its patch sites are
interpreted:

```lean
inductive SerializableRelocationPolicy where
  | forbidden
  | registered (dialect : StableId)

structure SerializableRelocatableSection where
  id : StableId
  alignment : Alignment
  permissions : SectionPermissions
  relocationPolicy : SerializableRelocationPolicy
  contents : ByteArray
```

The numeric relocation kind is scoped by the selected section's registered
dialect. The in-kernel object resolves that nominal dialect to the exact
target-owned decoder, positive patch width, arithmetic/encoding semantics, and
soundness laws used by its relocation certificate. Structural parsing checks
the policy tag and rejects every relocation whose patch section is
`forbidden`; semantic validation additionally rejects an unknown dialect or an
unknown kind within a known dialect. Section spelling, file extension, ambient
linker options, and digests are not dispatch authority. Two equal numeric kinds
under different dialects are intentionally different operations. This permits
heterogeneous objects while letting ordinary single-target objects select one
standard policy mechanically.

The target-independent import body has a small, first-order identity rather
than embedding a platform loader record or a Lean contract:

```lean
inductive SerializableImportSubject where
  | callable
      (signature : StableScopeId)
      (callable : StableId)
  | providerOperation
      (providerProfile : StableId)
      (operation : StableId)

structure SerializableImportEntry where
  localTarget : StableId
  subject : SerializableImportSubject
  abiContract : StableId

def canonicalImportKey (entry : SerializableImportEntry) : CanonicalBytes :=
  canonicalEncode (entry.localTarget, entry.subject, entry.abiContract)

theorem canonicalImportKey_injective :
    Function.Injective canonicalImportKey

structure SerializableImportManifest where
  entries : Vec SerializableImportEntry
  localTargetsUnique : PairwiseDistinct entries.localTarget
  canonicallyOrdered : StrictlyIncreasing canonicalImportKey entries
```

All identifiers are encoded by their structured components; a dotted display
name or digest is not an identity. `localTarget` is the stable object-local
symbolic target used by relocations. A callable subject names an exported
callable in an imported program signature. A provider subject names the exact
selected provider profile and operation. `abiContract` names the complete,
versioned ABI contract expected at that boundary. The rich signature, provider
dictionary, ABI value, and their laws remain in the in-kernel object; a
`PayloadImportsSignature` proof resolves every serialized name to those exact
values and proves that every imported relocation uses the matching
`localTarget`.

Relocations keep one uniform target index into the object symbol table. The
symbol table therefore has two disjoint entry forms: a defined symbol carries
its section-relative extent and local/exported visibility, while an imported
symbol carries an index into `SerializableImportManifest` and no section or
extent. Its local symbol name is exactly the referenced import entry's
`localTarget`. Structural validation checks the correct arm, checks every
import index, checks that each imported symbol's local name equals the indexed
entry's `localTarget`, and rejects a defined symbol masquerading as an import
(or the reverse). This avoids a second relocation target namespace while
making an external call representable; a table containing only local/exported
defined symbols cannot implement the import design.

Manifest semantics are a finite map keyed by `localTarget`, not authored list
order. `canonicalImportKey` encodes the complete structured entry: its local
target, tagged subject and all subject components, and ABI-contract key. The
`canonicalImportKey_injective` theorem follows from injectivity of those
component encodings and disjoint subject tags. The wire writer sorts entries by
that key. The reader checks that order and the separate `localTarget`
uniqueness condition, so permuting an otherwise identical import set is not a
second canonical payload. Multiple relocations may share one imported symbol,
and final linking may intern distinct local imports only after proving their
subjects and ABI contracts identical.

The manifest deliberately contains neither a final loader spelling nor a slot
address. A final platform link maps a provider subject to a format-specific
physical import identity (for example DLL plus name-or-ordinal), proves that it
implements the same nominal operation and ABI contract, and then derives and
lays out any GOT/IAT/PLT slot. The selected import environment and derived slot
identity enter the final loaded/raw coupling. This separation permits the same
`.gobj` grammar to carry Win32, ELF, WASI, bare-metal, and inter-object imports
without making a Windows import tuple the universal object identity.

The binary reader validates framing, tags, structured identifier encodings,
and uniqueness. It cannot manufacture the semantic lookup proofs. Unknown
subject variants fail under the declared format version; future variants
require a new version or an explicitly registered length-delimited extension
with its own parser laws.

The existential/private specification is lawful here because an object claims
only its exported interface. It is not lawful at the final product gate, where
the exact precious root specification is known and retained.

An object carries symbolic relocation targets, section alignment and
permissions, exported/imported ABI contracts, provider demands, resource and
obligation summaries, and a hierarchical machine certificate. Its proof does
not mention a final image base or offsets of unrelated objects.

`GobjPayload` is deliberately proof-free and first-order serializable.
`VerifiedObject` is deliberately not serializable: it contains arbitrary Lean
types, specifications, and kernel proof terms. The payload is useful for linking
only through the exact equality stored by its in-kernel `VerifiedObject`.

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

structure ResolvedGobj {sig : ProgramSignature}
    (object : VerifiedObject sig) where
  bytes : ByteArray
  parsed : parseGobj bytes = .ok object.payload

def linkVerifiedResolved
    (plan : LinkPlan root signatures)
    (objects : HArray VerifiedObject signatures)
    (files : HArray (fun i => ResolvedGobj objects[i]) signatures) :
    Except LinkError (VerifiedProgram root)
```

The linker checks exact symbol resolution, signature/ABI compatibility,
provider coherence, section permissions/alignment, relocation range and
encoding, import synthesis, resource/obligation composition, and entry/export
selection. Its connection theorem proves that parsing/loading the emitted image
produces the linked machine program assembled from those exact objects and that
the signature composition refines `root`.

`linkVerifiedResolved` is a streaming implementation of the same theorem. Each
file is untrusted until `parseGobj` returns the payload definitionally owned by
the corresponding imported certificate. The equality rewrites file data to the
certified payload before symbol resolution, relocation, or output construction.
The resulting `VerifiedProgram` and `emitProgram` are therefore still derived
from the in-kernel objects. A digest, certificate name, or successful structural
parse cannot supply `ResolvedGobj`.

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
interface edits, cache hits, proof bytes, and peak memory using the structural,
graph-simulation, and calibrated-real-build ratchet in
[OLEAN_SHARDING.md](OLEAN_SHARDING.md). The design target is work proportional
to the changed shard plus affected ancestor/interface closure, with logarithmic
or bounded index lookup; no fixed numeric timing or giant instruction corpus is
claimed before measurement.

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

`.gobj` is an optional deterministic serialization of `GobjPayload`. It contains
no proof and no executable certificate reference. It obeys the corpus laws:

- `parseGobj (writeGobj payload) = .ok payload`;
- every successful parse satisfies the binary grammar and structural
  invariants; and
- a file is accepted for a certificate only through
  `parseGobj bytes = .ok object.payload`.

The initial trusted workflow imports the exact certificate `.olean`, parses the
`.gobj`, and kernel-checks the payload equality used by `ResolvedGobj`. A truly
standalone proof-carrying linker would require a separately specified proof
format and verified proof checker; it is not claimed by this design. A
standalone unverified linker may produce diagnostic bytes, but those bytes are
not the output of `emitProgram` and carry no Grass correctness claim.

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
