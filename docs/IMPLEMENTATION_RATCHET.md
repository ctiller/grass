# Implementation ratchet for the design spikes

Status: normative future command and evidence contract. None of the commands or
outputs in this document is claimed to exist yet. Implementing them belongs to
the library phase, which is explicitly outside the present design exercise.

## Purpose

Design approval means the displayed interfaces can be implemented without a
new foundational choice. Implementation approval additionally requires
reproducible evidence that exact authored source expands, verifies, emits,
round-trips, rejects the named mutations, and rebuilds within its declared
`.olean` dependency cone.

All five spikes use one command surface and one schema family. A spike may add a
domain report, but may not invent an alternate proof or artifact route.

## 1. Versioned command surface

The future executable is invoked through the pinned Lake environment:

```text
lake env grass spike mirror     --spike <1..5> --out .grass/reports/<spike>/mirror.v1.json
lake env grass spike elaborate  --spike <1..5> --out .grass/reports/<spike>/elaboration.v1.json
lake env grass spike verify     --spike <1..5> --out .grass/reports/<spike>/verification.v1.json
lake env grass spike artifact   --spike <1..5> --out .grass/reports/<spike>/artifact.v1.json
lake env grass spike mutate     --spike <1..5> --fixture <key> --out .grass/reports/<spike>/mutations/<key>.v1.json
lake env grass spike locality   --scenario <key> --out .grass/reports/locality/<key>.v1.json
```

Every command records the Git tree identity, Lean/Lake/tool versions, target
profile, imported semantic-environment root, normalized command arguments, and
schema version. It exits nonzero if its certificate phase fails or if its output
cannot be written atomically. JSON is a review projection; the referenced
kernel-checked declaration and verified object remain proof authority.

`mirror` may be implemented first by `check-spike-sources.ps1`, but the eventual
command must emit the same classified manifest rather than merely print a pass
line.

## 2. Common report envelope

```lean
structure EvidenceEnvelope (payload : Type) where
  schema : SchemaId
  schemaVersion : Nat
  spike : Option SpikeId
  gitTree : GitTreeId
  lean : LeanVersion
  lake : LakeVersion
  grass : ToolVersion
  profile : Option ProfileId
  semanticEnvironment : SemanticEnvironmentRoot
  command : NormalizedCommand
  started finished : Timestamp
  payload : payload
  payloadDigest : Digest payload
```

Timestamps and durations are evidence metadata and never enter theorem types or
cache applicability. Stable identities are nominal IDs plus exact checked
content; hashes locate content but do not prove it.

## 3. Phase reports and acceptance

### 3.1 Mirror

`MirrorReportV1` contains the authored-file manifest, classified Markdown block
manifest, normalized content digest for each side, duplicate identities, missing
files, extra files, and mismatches.

Acceptance:

- every fenced block has exactly one valid classification;
- every `authored file=` block matches one `.lean` file byte-for-normalized-byte;
- no authored `.lean` file is absent from the document;
- generated and proof-sketch blocks cannot masquerade as authored source; and
- authored specification and realization line/module/declaration counts are
  recomputed from this manifest.

### 3.2 Elaboration and source closure

`ElaborationReportV1` contains:

```lean
structure ElaborationReportV1 where
  authored : ClassifiedSourceManifest
  scopes : Array ElaboratedSourceScope
  constructors : Array ConstructorExpansion
  fragments : Array SourceFragmentClosure
  aggregate : HierarchicalClosedAsmSource
  joins : ExactDiscoveredJoinSelection
  imports symbols relocations : HierarchicalManifest
  citations : InstructionAnchorManifest aggregate.rawListing
  sourceMap : HierarchicalSourceMap
  errors : Array SourceElaborationError
```

Acceptance requires no errors, exact fragment/macro/static/import/reference
coverage, exact join selection, total source maps, and a bounded-fanout aggregate
tree. Scope elaboration reports the selected entry/frontier/imported-call values
and the mechanically discovered occurrence set. It must not choose an algorithm
scope, representation, invariant, cancellation policy, or cross-ISA connection.

### 3.3 Verification

`VerificationReportV1` contains the staged portable, projection, provider,
machine, and artifact requirement-key families and origin maps; local
`AssemblyCheckReport`s; model bindings; process/cancellation/resource/obligation
certificates; composition nodes; residual goals; axiom audit; and the final
kernel declaration name and normalized type.

Acceptance requires:

- every requirement key discharged once at the correct stage;
- every local report has an exact reviewed empty residual allowlist;
- no `axiom`, `sorry`, `admit`, execution-as-proof, or `native_decide` proof;
- `native_decide` may appear only in explicitly non-proof test tooling;
- universal input/API/provider results remain universally quantified;
- the exact source hierarchy is retained by the machine certificate; and
- the final declaration has type `VerifiedProgram exactSpec`.

### 3.4 Artifact

`ArtifactReportV1` contains verified-object identities, streamed link plan,
section/import/export/relocation/unwind manifests, exact serialized ranges,
writer/parser reports, loader connection, emitted digest and path, and the
executable observation connection.

Acceptance requires the common writer law `parse (write x) = .ok x`, the
format-specific accepted-input conformance law, exact source-to-object-to-bytes
adjacency, valid ASLR relocations and standard permissions, and successful
loading under the selected profile model. Running the artifact is a probe, not
proof.

### 3.5 Mutation

Each mutation is a semantic edit applied to an isolated temporary worktree. Its
manifest names the exact source transformation, expected first failing phase,
expected diagnostic key, allowed rebuild cone, and required reusable modules.
`MutationReportV1` records actual first failure and build actions.

Acceptance requires the expected phase/key, not merely any failure. A mutation
which reaches a later phase has crossed an unsound boundary. A mutation expected
to preserve correctness must instead complete and remain within its declared
invalidation cone.

## 4. Required spike fixtures

### Spike 1: Hello World

Positive fixture: the logical `TextLine` projects to the exact UTF-8/CRLF static
object, all partial writes commit the same ordered byte sequence, every admitted
provider result reaches the declared outcome, and the PE writer/parser/loader
chain closes.

Required mutations:

| Key | Edit | First failure |
|---|---|---|
| `hello.payload.byte` | alter one projected static byte | text-projection/static-object adjacency |
| `hello.payload.count` | pass a count different from derived object length | typed write slice |
| `hello.partial.zero` | treat successful zero-byte write as progress | progress/partial-write model |
| `hello.stack.shadow` | remove required Win64 shadow space | ABI call-site certificate |
| `hello.relocation` | replace symbolic IAT reference with an invalid fixed address | relocation/source closure |

### Spike 2: Sort

Positive fixture: arbitrary partial stdin chunks parse under the selected line
grammar; allocation failure emits no bytes; the selected descriptor scope
refines the banked stable-sort model; and partial output writes preserve order.

Required mutations:

| Key | Edit | First failure |
|---|---|---|
| `sort.scope.escape` | redirect one merge edge outside `sortAlgorithmScope` | scope frontier coverage |
| `sort.rep.field` | swap descriptor offset and length fields | representation adjacency |
| `sort.equal.right` | choose the right descriptor on equality | assembly-to-stable-model proof |
| `sort.parser.suffix` | drop normalized final unterminated line | parser requirement witness |
| `sort.alloc.output` | write before the allocation barrier completes | resource/failure observation |

### Spike 3: Gzip

Positive fixture: every input chunking produces one valid gzip member whose
inflation is the input; committed failure output remains a construction prefix;
resident memory is input-length independent; and the codec callable scope
refines the banked fixed-32K model while importing exactly one abstract output
sink.

Required mutations:

| Key | Edit | First failure |
|---|---|---|
| `gzip.scope.flush` | absorb `flush_output` without its imported sink contract | callable-scope import coverage |
| `gzip.rep.dictionary` | exchange `head` and `prev` arena fields | representation adjacency |
| `gzip.distance.future` | admit a candidate at or after the current position | assembly-to-LZ77 model proof |
| `gzip.crc.bit` | alter the reflected CRC polynomial step | CRC model adjacency |
| `gzip.writer.prefix` | discard already committed bytes on write failure | failure observation theorem |

### Spike 4: HTTP/2 server

Positive fixture: the selected HTTP/2 package, grammar, frame/state/error matrix,
HPACK state, connection/stream flow credits, fixed storage, partial socket I/O,
cancellation, and shutdown all close against the exact x86 source and WinSock
provider profile.

Required mutations include one member of every portable protocol requirement
key family plus:

| Key | Edit | First failure |
|---|---|---|
| `h2.frame.oversize` | use the peer send limit as the local receive limit | protocol/profile projection |
| `h2.headers.scheme` | accept selected non-CONNECT GET without `:scheme` | request-field state machine |
| `h2.content_length` | accept END_STREAM with a mismatched body count | message validity theorem |
| `h2.credit.double` | return stream or connection credit twice | resource/flow-credit invariant |
| `h2.cancel.blocking` | add an uncovered blocking provider call | cancellation CFG elaboration |
| `h2.hpack.atomic` | expose cancellation inside private table mutation | atomic-region certificate |
| `h2.join.edge` | add a predecessor to a selected join | join-selection key family |
| `h2.partial_send` | commit bytes other than the returned prefix | socket/write refinement |

The protocol package maintains its own mutation coverage theorem: every
portable key has at least one rejecting mutation or a positive independence
fixture. The application does not hand-maintain that list.

### Spike 5: spinning cube

Positive fixture: the portable cube process, staged subsystem blend, Win32 host,
Vulkan provider calls, x86 source, two SPIR-V modules, callback state, floating
rotation relation, ownership cleanup, cross-ISA occurrence chains, and PE ranges
compose into one `VerifiedProgram spec`.

Required mutations:

| Key | Edit | First failure |
|---|---|---|
| `cube.blend.abstract` | leave one reachable descendant abstract | staged frontier closure |
| `cube.provider.conflict` | select Metal for one graphics demand | coherent provider plan |
| `cube.callback.clear` | omit the `WM_NCDESTROY` state-pointer clear | callback/state connection |
| `cube.shader.range` | point `pCode` at the other embedded range | cross-ISA static/call adjacency |
| `cube.shader.handle` | put the fragment handle in vertex pipeline stage 0 | cross-ISA returned-handle use |
| `cube.shader.entry` | change `pName` without changing the proved entry | cross-ISA entry-point connection |
| `cube.rotation.range` | admit a clock value outside the numeric theorem domain | target numeric projection |
| `cube.cleanup.order` | destroy a parent before an owned child | obligation/ownership ledger |

## 5. `.olean` locality ratchet

The `locality` command implements [OLEAN_SHARDING.md](OLEAN_SHARDING.md). It
does not generate a giant instruction program. Required scenarios are:

```text
cold
no-op
leaf-instruction
leaf-invariant
exported-boundary
specification-key
layout-only
provider-profile
aggregate-rebalance
```

`BuildExecutionReportV1` records the abstract dependency graph, changed inputs,
planned actions, actual module/facet actions, re-elaborated modules,
kernel-checked declarations, imported/reused `.olean` files, `.olean` and proof
bytes, `.gobj` bytes, source/artifact bytes scanned and written, cache outcomes,
wall time, and peak memory.

The structural theorem proves that a body edit preserving `Sig` changes only
the leaf implementation/certificate/object and aggregate ancestor identities.
A large compact graph simulation checks affected-node computation and bounded
fanout. Representative real builds are increased only until import,
elaboration, kernel, encoding, and linking cost curves are measurable.

Acceptance is structural:

- a leaf-body edit reuses caller and sibling `.olean` files whose signatures are
  unchanged;
- only the changed leaf certificate and bounded aggregate path are re-proved;
- an exported-boundary edit rebuilds exactly its semantic dependent cone;
- a layout-only edit does not reopen portable or algorithm proofs;
- no public theorem type contains a complete descendant instruction stream;
- no aggregate imports every leaf directly; and
- peak memory remains bounded by configured shard/fanout plus streaming link
  buffers.

Timings are recorded for regression, not fixed in advance. If ordinary Lean
module overhead defeats the selected shard size, the policy is coarsened and
remeasured; no unchecked proof cache or custom kernel path is permitted.

## 6. Sign-off

Design review checks that every demanded command input, report field, mutation,
and first-failure boundary is expressible by the documented interfaces.
Implementation review runs the commands in a clean checkout, retains the
reports and certificates, repeats the rejecting mutations, and compares the
actual locality graph with the declared one.

Failure of a spike-specific instruction or constant that the implemented type
checker immediately exposes is an ordinary implementation repair. Failure which
requires inventing a new semantic layer, proof authority, scope model,
representation junction, process law, artifact connection, or invalidation
boundary reopens the design.
