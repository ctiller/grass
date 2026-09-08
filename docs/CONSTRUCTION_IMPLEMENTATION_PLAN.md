# Construction and lowering implementation plan

Status: working plan owned by the `g-construct` implementation agent. This is
a tier-four scheduling document. It implements the contracts in
[ASSEMBLY_CONSTRUCTION.md](ASSEMBLY_CONSTRUCTION.md) and
[INSTRUCTIONS.md](INSTRUCTIONS.md), especially `INSTRUCTIONS.md` sections 4
and 5; it does not amend those normative documents. `g-design` remains the
normative owner of `ASSEMBLY_CONSTRUCTION.md`.

## 0. Ownership boundary

This plan exclusively owns:

- `Grass/CFG/**` and `Tests/CFG/**`: block contracts, edges, joins, loop
  obligations, calls, stack shapes, and local CFG composition;
- `Grass/Construct/**` and `Tests/Construct/**`: source/layout values,
  placement, verified finite instruction-fragment generators, expansion, and
  checked lowering; and
- `Grass/Unsafe/**` and `Tests/Unsafe/**`: the narrow raw boundary for
  construction, import, stepping, and emission.

The shared files `lakefile.toml` and `.github/workflows/library.yml` are changed
only to expose and gate these modules. In `docs/INSTRUCTIONS.md`, the macros and
authored-CFG sections are this plan's implementation surface. Changes to
`docs/ASSEMBLY_CONSTRUCTION.md` are coordinated with `g-design` and remain
normative design work rather than implementation-plan authority.

This plan does not own instruction semantics, target encoding tables, ABI
facts, memory or obligation semantics, platform contracts, artifact formats,
or whole-program verification. It consumes their exported contracts. In
particular:

- `Grass.Op` supplies closed instruction facets and the executable step;
- `Grass.Memory` and `Grass.Obligation` supply machine state and effects;
- ISA owners supply typed operations, encoders, decoders, and citations;
- ABI owners supply call-frame, preservation, alignment, and unwind facts;
- artifact owners consume an exact raw hierarchy and produce a file; and
- `Grass.Verify` consumes the construction certificate but decides whether a
  whole program satisfies its specification.

## 1. Non-negotiable invariants

The implementation is organized around six constraints from the normative
documents.

1. Construction is not proof authority. A generator returns a theorem-backed
   value, a certificate checked by a proved checker, or explicit residual
   goals. Merely evaluating Lean code establishes nothing about emitted code.
2. Lowering is total. It either returns one complete raw hierarchy and total
   source map or a typed construction error; there is no usable partial output.
3. Expansion is exact and inspectable. Calls, control-flow exits, faults,
   memory accesses, obligations, cancellation points, clobbers, and generated
   labels cannot be hidden by a macro or fragment constructor.
4. CFG discovery is structural. Authors do not maintain parallel label,
   predecessor, join, cancellation, or relocation tables. Derived manifests
   are exact projections of the same source tree.
5. Logical contracts and physical placement remain separate. Register and
   stack-slot choices can change by replacing a placement proof without
   restating stable mathematics.
6. Unsafe code is downstream and narrow. Raw constructors and import/emission
   adapters may not manufacture `VerifiedFragment`, `ImplementsBlock`, source
   closure, or whole-program verification evidence.

## 2. Layering and public seams

The intended dependency direction is:

```text
Grass.Core / Grass.Semantics / Grass.Memory / Grass.Obligation / Grass.Op
                                  |
                                  v
                              Grass.CFG
                                  |
                                  v
                            Grass.Construct
                                  |
                                  v
                              Grass.Unsafe
                                  |
                                  v
                    ISA / ABI / artifact integrations
```

`Grass.CFG` owns semantic structure and must not import `Grass.Unsafe`.
`Grass.Construct` may consume CFG contracts and ISA/ABI interfaces, but its
certificate-bearing modules must not depend on raw emitters. `Grass.Unsafe`
may erase, decode, step, or serialize already selected values; no module above
it recovers a theorem by unfolding an unsafe implementation.

The public seams are deliberately small:

| Seam | Producer | Consumer | Required claim |
|---|---|---|---|
| operation summary | ISA / `Grass.Op` | CFG symbolic checking | complete facets and step relation |
| block contract | CFG | authored source and verifier | typed entry plus total exit family |
| CFG manifest | CFG discovery | closure and review tooling | exact labels, edges, joins, cycles, calls, and terminals |
| placement | Construct | CFG contracts and operands | compatible physical locations represent logical fields |
| verified fragment | Construct | authored source | finite exact expansion and all-exit local correctness |
| raw hierarchy | Construct | Unsafe / artifact writer | exact recursively concatenated writer input |
| imported hierarchy | Unsafe decoder adapter | CFG / Construct | decoded instructions plus complete target evidence or a typed rejection |

## 3. Milestones

### C0 — Contract kernel and CFG identity

Create the smallest reusable vocabulary under `Grass/CFG/`:

```text
Grass/CFG/Contract.lean   block entry/exit contracts and exit classification
Grass/CFG/Graph.lean      block identity, labeled edges, terminals, predecessors
Grass/CFG/Manifest.lean   derived finite manifests and closure predicates
```

The types remain generic over machine state, events, and instruction summaries.
This prevents the core graph library from becoming x86-specific while allowing
the first executable instantiation to use `Grass.Memory.MachineState` and
`Grass.Op.step`.

Exit criteria:

- every edge has one source, target or terminal disposition, and exit tag;
- duplicate block identities and unresolved direct targets are rejected;
- predecessor discovery agrees exactly with the source block list;
- straight-line single-predecessor blocks can inherit an entry contract; and
- fixtures reject a missing target, duplicate label, and mismatched exit tag.

### C1 — Joins, loops, calls, and stack shapes

Extend the CFG kernel without introducing an authored parallel manifest:

```text
Grass/CFG/Join.lean       structural join discovery and exact selection
Grass/CFG/Loop.lean       back-edge obligations, measures, and frontiers
Grass/CFG/Call.lean       local/external call edges and return families
Grass/CFG/Stack.lean      abstract stack delta and stack-shape compatibility
Grass/CFG/Compose.lean    block checking and `SubCFG.plug`
```

Acyclic single-predecessor targets take inferred contracts. Shared targets are
selected exactly once. Every cyclic strongly connected region supplies an
invariant and either a decreasing measure or an admitted liveness frontier.
A call exposes normal, fault, pending, cancellation, interruption, violation,
and unwind outcomes supported by its selected contract; no generic default
silently invents an outcome.

Exit criteria include rejection fixtures for an uncovered back edge, a call
made with an incompatible stack shape, a missing non-normal return, and an edge
that bypasses stack-scope elimination.

### C2 — Logical placement and static layouts

Build layout and placement values under `Grass/Construct/`:

```text
Grass/Construct/Layout/Core.lean       representation and alignment profiles
Grass/Construct/Layout/Struct.lean     fields, offsets, padding, and lookup
Grass/Construct/Layout/Array.lean      stride and checked indexing
Grass/Construct/Layout/Stack.lean      lexical objects and frame demands
Grass/Construct/Placement.lean         logical-field to machine-location proofs
```

The first slice covers ordinary nonempty structs, arrays, named stack slots,
and explicit fixed offsets. Packed values, unions, bitfields, flexible tails,
overlays, and bounded dynamic stack objects arrive as separate constructors
with separate proof obligations; they are not guessed by the ordinary layout
deriver.

Exit criteria include executable concrete offsets and reusable theorems for
alignment, containment, pairwise disjointness, lookup exactness, array stride,
and literal-offset correspondence. Negative fixtures cover duplicate names,
overflow, invalid alignment, overlap, an escaping lexical address, and a live
loan or obligation at scope exit.

### C3 — Verified finite fragments

Create the theorem-family abstraction described by
`ASSEMBLY_CONSTRUCTION.md`:

```text
Grass/Construct/Fragment/Raw.lean       finite raw lists and hierarchies
Grass/Construct/Fragment/Effect.lean    derived complete effect summaries
Grass/Construct/Fragment/Verified.lean  exact expansion and local correctness
Grass/Construct/Fragment/Compose.lean   sequencing and all-exit composition
Grass/Construct/Fragment/Registry.lean  explicit constructor closure
```

Literal instructions and generated fragments are peers with one result type.
The registry is a dependent input to authored source, never an ambient search.
Composition frames untouched state only through exported semantic lemmas.

Exit criteria: exact expansion, total exit coverage, source-location coverage,
reference closure, citation coverage, complete effect derivation, and mutation
fixtures showing that a changed expansion, omitted clobber, or dropped fault
exit breaks the certificate.

### C4 — Authored source and checked lowering

Implement the stable term-level surface before adding punctuation-saving
syntax:

```text
Grass/Construct/Source/Ast.lean       blocks, annotations, literals, and splices
Grass/Construct/Source/Discover.lean  labels, joins, loops, calls, and demands
Grass/Construct/Source/Close.lean     hierarchical source closure
Grass/Construct/Lower.lean            total structured-to-raw lowering
Grass/Construct/Report.lean           expanded view, manifests, and residuals
```

The elaborator syntax (`asm_source`, `asm_fragment`, annotation forms, and
typed splices) is built only after these term-level values have stable tests.
Generated declarations remain alpha-normalized per block and separately
cacheable. Diagnostics name the source instruction, edge, phase, contract, and
residual proposition.

The staged checker follows the normative phase order: elaborate, symbolic,
frame, arithmetic, ghost, close. A phase cannot claim a later phase's work, and
reviewed residual allowlists compare by exact keys.

Exit criteria: a mixed literal/generated source closes hierarchically; changing
one leaf invalidates only that leaf and ancestors; every generated source item
maps to raw output; and missing invariants, provider outcomes, and semantic
correspondence remain residuals in the prescribed phases.

### C5 — ABI-transparent stack and call generators

Instantiate C1-C4 against the merged ABI interfaces:

```text
Grass/Construct/StackObject.lean
Grass/Construct/Frame.lean
Grass/Construct/CallFrame.lean
```

`enter`, `leave`, `save`, `restore`, `spill`, `reload`, `withStack`, and
`withCallFrame` are transparent verified fragment constructors. They consume
rather than restate ABI facts. On Win64 the selected frame must account for
shadow space, pre-call alignment, stack arguments, saved nonvolatile state,
call-loan phases, and exact unwind correspondence. A checked call-frame session
must contain a compositional prepared-to-closed transition run: acquisition
records the exact nonempty loan set, return or unwind records the exact released
set, and closure records restoration of exactly the selected saved registers.
The run exposes those actions in exact lifecycle order and run concatenation
concatenates action traces exactly. Every completed session is classified as
exactly acquisition, matched release through normal return or unwind, and exact
saved-register restoration. Valid prepared and closed endpoints alone are
insufficient. A literal call remains legal and is checked against the same
pre-call contract without implicit rewriting.

`Grass.Construct.StackObject` supplies the checked base for stack-object
operations: a `StackObjectRef` carries membership in one exact
`CheckedStackLayout`, and a `CheckedStackSlice` carries a nonempty relative
range bounded by that object. Nominal lookup returns a `NamedStackObjectRef`
carrying exact requested-name equality. The absolute frame-relative range is
derived and proved to remain within the checked layout; malformed layouts,
missing objects, zero-size slices, and out-of-bounds slices return structured
errors.

`Grass.Construct.StackObjectSource` is the transparent machine seam over that
checked base. Machine code constructors receive only the exact derived
`ByteRange`; direct and named load/store helpers expose literal source
expansion equal to those constructors and provide no semantic certificate.
`Grass.Construct.StackObjectVerified` is the proof-bearing companion: its
machine backend supplies each `VerifiedFragment` and exact equality to the
transparent checked-slice source, while construction only projects those
witnesses.
`Grass.Construct.FrameStackObject` reuses the exact checked local layout from a
`CheckedWin64Frame`, adds the derived shadow and stack-argument base to each
checked slice, and proves the resulting post-prologue RSP-relative range stays
within the selected frame subtraction.
`Grass.Construct.FrameStackObjectVerified` requires machine-supplied verified
fragments whose sources are exactly the derived frame-offset load/store
sources; its public operations only project those witnesses.
`FrameSourceBackend.save` and `FrameSourceBackend.restore` expose the exact
selected push order and reverse pop order independently of `enter` and `leave`;
`FrameVerifiedBackend` requires separate verified witnesses and exact-source
equalities for both operations.

The lexical `withStack` path begins with `Grass.Construct.StackScope`: an exact
ordered ledger covers every contract exit by identity and proves that each exit
has no escaping address, live loan, or live obligation. The eventual
provenance-indexed eliminator must consume this certificate; it may not infer
closure from a normal exit alone.
`Grass.Construct.StackScopeToken` supplies the generative identity side: it
threads a monotone fresh supply, ties each minted token to one declared scope in
an exact checked layout, and indexes object bindings by that token only when the
object's declared scope matches. Physical memory provenance remains owned by
the execution model rather than being fabricated by construction.
`Grass.Construct.StackScopeSession` composes those prerequisites: it performs
one exact mint and checks an all-exit ledger whose resource family is indexed by
the resulting nominal identity through `StackScopeResource`. It preserves the
token and advanced supply for the later eliminator and proves freshness,
issuance, non-reissue, exact exit coverage, and closure. It is not itself
`withStack`: hiding the token while returning a verified outer fragment still
requires the execution model's provenance interpretation and elimination law.
`Grass.Construct.StackScopeNest` threads an outer session's exact output supply
into an inner session, permits the inner payload to depend on the outer token,
requires the inner declared scope's parent to equal the outer declared scope,
and proves the two sequential tokens distinct. This supplies the nominal,
lexical, and all-exit composition for nested binders while leaving the same
provenance elimination obligation explicit.
`Grass.Construct.StackScopeCFG` injectively maps declared layout scopes into the
stable CFG scope vocabulary and pairs a checked session with exact stack-shape
entry. Its all-exit theorem combines the session's resource closure with LIFO
restoration to the exact outer `StackShape`, closing the structural edge-bypass
seam without conflating stable authored identity and fresh occurrence identity.
`Grass.Construct.StackScopeCFGNest` checks nested sessions in lexical order,
proves their stable CFG identities distinct, exposes the exact two-scope stack
head, and combines both all-exit closure certificates with exact two-step LIFO
restoration. Outer and inner entry failures retain their exact lexical stage.
`Grass.Construct.Scratch` provides the generic term-level prerequisite for
`withScratch`: it selects the first non-live register from an exact ordered,
duplicate-free candidate set and passes a handle to a fixed-contract verified
body without adding hidden source. It deliberately does not derive liveness;
the machine backend must connect the supplied live set to its effect model
before the final authored macro can rely on the selection.
`Grass.Construct.ScratchLiveness` makes that connection explicit:
`CheckedScratchContext` requires the backend's liveness relation to equal the
request's live set at every state admitted by the body contract. The resulting
`withLiveScratch` binder retains the fixed contract and exact body source; it
still delegates instruction correctness to the supplied `VerifiedFragment`.
`Grass.Construct.Source.Containment` supplies the proof-only containment metadata
surface from `INSTRUCTIONS.md` section 5. Each annotation carries an exact
violation class and finite affine return envelope and must attach to one literal
CFG edge or the exact final instruction origin of its block. Duplicate and
unattached sites are rejected, while erasure theorems prove the projected CFG,
located instruction expansion, and instruction count unchanged.
`Grass.Construct.Source.Label` supplies the hygienic macro-local label API:
opaque tokens come from a monotone fresh supply and remain distinct even when
their diagnostic hints match. An injective `LabelAlphaModel` resolves local
tokens into stable manifest `BlockId`s while preserving literal stable labels;
sequential mints are proved distinct both before and after normalization.
`Grass.Construct.Source.Alpha` carries literal or local labels at the authored
entry, block declarations, and direct edges, resolves every position through
one alpha model, and checks structural closure of the resulting ordinary AST.
Normalization theorems preserve exact instruction bodies and review annotations;
failed closure reports the normalized entry, block identities, and unresolved
targets without manufacturing a partially verified program.
`Grass.Construct.Source.Manifest` derives the command-facing per-block manifest
from that ordinary AST: canonical block and exit identities, exact outgoing
edges, structural instruction origins, and counts remain in authored order.
Projection and lookup theorems tie every field back to the single AST, so the
manifest cannot become a second independently maintained source description.
`Grass.Construct.Source.Elaborate` composes alpha-normalization, structural graph
closure, and manifest derivation into one checked term-level result. Its fields
and public theorems retain the exact normalized AST, manifest, instruction list,
annotations, entry, block identities, and counts. A future command/parser layer
may construct the pre-alpha value but cannot bypass these closure checks.
`Grass.Construct.Source.ElaborateContainment` adds the containment-specific gate:
ordinary structural elaboration must succeed before duplicate or unattached
containment sites are checked on the exact normalized AST. The result retains
both certificates and exposes graph and located-instruction invariance under
metadata erasure; failures retain their structural or containment stage.
`Grass.Construct.Link.Raw` is the format-neutral producer seam consumed by
Artifact. It owns section-relative logical bytes and zero fill, requested class/
permissions, definitions, parameterized relocations and external identities,
entry candidates, and exact source-map ranges, with executable structural
validation. `.gobj`, COFF, PE, final placement, and relocation/import policy stay
Artifact-owned; the ISA/ABI backend supplies the exact source/encoding relation.
`Grass.Construct.Fragment.Registry` supplies C3's explicit constructor closure:
one finite dependent input carries heterogeneous parameter types and verified
generators, duplicate identities are rejected before resolution, and a typed
application can only name a constructor resolved from that exact closure. The
selected certificate is wrapped with its exact constructor origin without
changing its instruction expansion; there is no ambient namespace registry.
`Grass.Construct.Source.ConstructorClosure` derives every generated constructor
occurrence directly from the authored hierarchy, retaining its block, parent
generator chain, and child path even when the generated body is empty. A source
advances only with ordinary CFG closure and no occurrence unresolved by its
exact checked constructor input; structural failures precede constructor
diagnostics, preserving the staged-checking order. Nominal closure is not
expansion authority: a separate `CertifiedConstructorSource` requires every
generated node body to equal one typed application of its resolved constructor.
`Grass.Construct.Source.ConstructorElaborate` composes that gate with ordinary
alpha-normalization and manifest derivation. Its staged error preserves alpha/
CFG failure priority, its success retains exact pre-alpha instructions and the
same normalized AST used by constructor closure, and its certified companion
adds exact typed-application correspondence without promoting nominal lookup.
`Grass.Construct.Source.ConstructorLower` then requires a separate `VerifiedAst`
over that exact normalized source before lowering. Constructor identity and
exact generated bodies remain provenance evidence; neither is silently promoted
into block-local semantic correctness.
`Grass.Construct.Source.CallClosure` derives call occurrences from the exact
located instruction expansion, checks targets and return routes against the
containing graph block, requires each call to be the sole projection of that
block's final instruction, and reports stable block/origin/projection diagnostics.
Because state predicates are not executable equality, exact block-to-call
contract correspondence remains a separate proof-bearing certificate.
`Grass.Construct.Source.CallElaborate` composes that checker with ordinary
alpha-normalization and manifest derivation. Alpha/CFG failures retain priority
over call-route failures, and both sides are indexed by the same normalized AST;
the certified result adds exact block-to-call contract equality separately.
`Grass.Construct.Source.ConstructionElaborate` is the combined frontend gate:
one alpha-normalized AST passes CFG, constructor-closure, and call-route checks
in explicit stage order. Its certified result retains typed constructor
application equality and block-to-call contract equality as separate proofs.
`Grass.Construct.Source.ConstructionLower` adds independently supplied
`VerifiedAst` evidence over that same normalized source. Total lowering retains
exact graph, source locations, and original pre-alpha instructions while both
constructor and call certificates remain separately inspectable.

The Spike 1 call/partial-write loop is the first acceptance fixture. Spike 2's
named layouts and reusable short fragments are the next one.

### C6 — Unsafe adapters

Keep raw operations visibly separated:

```text
Grass/Unsafe/Construct.lean  unchecked raw AST creation with explicit taint
Grass/Unsafe/Import.lean     decode and control-target evidence boundary
Grass/Unsafe/Step.lean       executable stepping adapter
Grass/Unsafe/Emit.lean       raw hierarchy streaming adapter
```

Unsafe values carry no certificate by construction. Promotion requires a
separately checked theorem or checker result in `Grass.Construct`; it is never a
cast or proof-erasing convenience. Imported indirect control flow is rejected
until annotations, relocation/symbol evidence, or analysis proves every target
belongs to the typed CFG.

The first C6 slice, `Grass.Unsafe.Construct`, wraps even malformed authored ASTs
in `UncheckedAst` with a mandatory primary `Taint` and an ordered additional
taint ledger. Its helpers perform no structural check and expose no promotion;
checked lowering still requires `Grass.Construct.Source.VerifiedAst`.

`Grass.Unsafe.Import` is machine-parametric: a machine owner supplies a
one-instruction decoder and exact control-target projection. The importer
requires each decode step to consume a nonempty exact prefix, rejects unresolved
direct or indirect targets against a `TargetPolicy` tied to one structurally
well-formed CFG and its derived block identities, and returns an `ImportedProgram`
whose concatenated instruction byte slices equal the original input and which
retains the exact policy used for acceptance. `ImportReadyFrom` additionally
retains the decoder-enforced consecutive offsets and nonempty slice for every
accepted instruction. Those byte-coverage facts are not an instruction-semantics
certificate.
`ImportedProgram.instructionAtByte?` exposes exact byte-to-instruction lookup;
its success and failure theorems identify membership plus containment and the
precise out-of-bounds boundary.
`ImportTargetsResolved` retains the importer's all-instruction target check, and
`ImportedProgram.controlTargetResolved` exposes it without re-running the
decoder or policy search.
`TargetPolicy.indirectEvidence?` exposes the exact finite evidence behind an
accepted indirect site; its lookup theorems retain requested-site identity and
prove every enumerated target belongs to the selected CFG.
`TargetPolicy.resolution?` converts target admission into a proof-bearing
`ResolvedControlTarget`: direct evidence exposes graph-block membership and a
concrete structural block lookup, while indirect evidence exposes the exact
selected finite target set. Its success is proved equivalent to
`TargetPolicy.resolves`; `resolutionOf` and
`ImportedProgram.controlTargetEvidence` recover the checked evidence value
without repeating decoder or policy validation.

`Grass.Unsafe.Step` maps imported instructions to the existing open
`Grass.Op.SomeOperation` package plus explicit context, cause, and fault-plan
inputs. Its one-instruction adapter is definitionally `Grass.Op.step`; the batch
runner threads only successful states, records the first rejection, and retains
the exact unattempted suffix. It introduces no parallel instruction semantics.

`Grass.Unsafe.Emit` streams a hierarchical fragment through one explicitly raw
instruction encoder. Every item retains its structural `SourceOrigin` and
consecutive byte offset, including zero-byte encodings; exact projection and
concatenation theorems tie the result to the original source while a mandatory
ordered taint ledger makes the absence of semantic and artifact certification
review-visible.
`Grass.Unsafe.EmitProgram` performs the corresponding operation on
`LoweredProgram`, retaining each containing block alongside `SourceOrigin` and
offset. Its verified-construction bridge proves the raw stream projects to the
original pre-alpha instructions and normalized CFG while keeping the byte
encoder explicitly tainted.
`Grass.Unsafe.EmitLink` validates consecutive offsets and rejects zero-width
encodings before projecting emitted items into `Link.SourceMapEntry` values.
Accepted ranges retain exact block/origin data and carry reusable positive-length
and emitted-byte-bound theorems. `entriesConsecutive` and
`entriesOrderedNonoverlap` additionally expose exact section order and
pairwise non-overlap. `entriesLengthSumExact` and `entryForByte` prove that
those ranges account for every emitted byte. `uniqueEntryForByte` combines
coverage with non-overlap to give each emitted byte exactly one source entry;
`entryAtByte?`, `entryAtByte?_eq_some_iff`, and `entryAtByte?_eq_none_iff`
provide the corresponding exact executable query. Artifact placement remains
downstream.
`Grass.Unsafe.EmitRelocatable` packages that checked stream as one initialized
format-neutral section with exact bytes and source ranges. It proves the generic
`RelocatableFragment.WellFormed` contract while leaving definitions,
relocations, externals, entry selection, serialization, and placement to their
independent producers and artifact-layer checks.
`fragmentSourceMapLengthExact` and `sourceEntryForInitializedByte` carry the
source-map completeness result through that format-neutral section projection;
`uniqueSourceEntryForInitializedByte` retains exact byte ownership there, and
`sourceEntryAtByte?` exposes its checked executable lookup.
Its `RelocatableEmissionPlan` overlay accepts those four symbolic metadata
tables independently, retains the exact checked bytes and source map, and
delegates their section bounds, symbol closure, and entry closure to
`checkRelocatableFragment`; it still performs no relocation or serialization.
`emitVerifiedConstructionRaw.bytesExact` and
`verifiedConstructionSectionBytesExact` close the source-to-writer-input
equation: initialized logical section bytes are the original pre-alpha authored
instructions encoded in order and converted through canonical `Byte.ofUInt8`.

Exit criteria include round trips for supported raw instructions, structured
errors for unknown/ambiguous bytes and targets, exact stepping agreement with
`Grass.Op.step`, and exact byte/list input passed to the artifact writer.

### C7 — Spike integration and proof economy

Integrate in increasing demand order:

1. Spike 1: literal Win64 x86-64 source, call frames, one loop, terminals, and
   exact writer input;
2. Spike 2: struct/frame layouts, placements, reusable fragments, and scopes;
3. Spike 3: multiple local call regions, packed layout, and nested loops;
4. Spike 4: large macro closure and process-loop contracts; and
5. Spike 5: heterogeneous source connections and device layouts.

Each spike enters the default build only when its imports elaborate. CI keeps
the source/document mirror gate active in the meantime. Acceptance records
expanded instruction count, residual goals, checker work, and rebuild cone so
concision does not hide proof or compilation cost.

## 4. Dependency order

The implementation order is C0, then C1. C2 can proceed once the core identity
and memory-range interfaces are stable. C3 depends on C0 and operation facets;
C4 depends on C1-C3. C5 depends on the ABI call-frame and unwind exports. C6
starts with adapters only after the corresponding checked value exists. C7 is
incremental and begins with the first usable C5 slice.

The current merged tree is sufficient for C0's generic identities, graph
discovery, and exit-family shape. The following boundaries must be consumed as
dependencies rather than copied locally:

- memory call-frame/loan laws for stack provenance and call transfer;
- complete ISA operation and encoder/decoder interfaces for concrete x86
  fragments;
- complete ABI register classes, call frames, and unwind correspondence;
- platform call outcomes and obligations; and
- the artifact writer's exact raw-input contract.

When one is absent, this agent publishes a typed dependency request and keeps
work on an independent milestone. It does not add a provisional competing
model under `Grass/CFG`, `Grass/Construct`, or `Grass/Unsafe`.

## 5. Verification and review loop

Every product slice runs, at minimum:

```text
lake build
lake env lean Tools/AxiomAudit.lean
pwsh -NoProfile -File ./audit-trust.ps1
pwsh -NoProfile -File ./check-doc-links.ps1
pwsh -NoProfile -File ./check-spike-sources.ps1
python Tools/DocstringAudit.py
git diff --check
```

Focused negative fixtures must fail for the exact claimed reason before their
positive counterpart counts as evidence. Certificate roots are added to the
trust audit as they become public. Generated raw views are compared exactly,
not only by successful execution.

Before formal nomination, the working loop uses fresh, context-free adversarial
review rounds. Findings are fixed and a new reviewer starts cold; the local
loop stops only when a fresh round finds nothing new. This is hardening evidence,
not independent review or merge authority. The bus nomination still names one
registered reviewer and one exact product commit.

## 6. First slice

The first product branch remains `refs/heads/agent/g-construct/construction-lowering`.
Its initial reviewable slice is C0 only: generic contracts, labeled direct
edges, exact predecessor/target discovery, and focused positive/negative
fixtures. It deliberately excludes elaborator syntax, x86 encoding, ABI frame
generation, raw emission, and whole-program verification. That keeps the first
claim small enough to review while establishing the identities every later
construction layer shares.

Completion of C0 changes this plan's active milestone to C1 and publishes the
exact exported declarations and checks on the agent bus. Any signature used by
another workstream is then treated as a separately reviewed boundary rather
than being silently rewritten during later lowering work.
