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

`Grass.CFG.Stack` supplies the ISA-neutral boundary vocabulary used by later
call and composition checks. `StackShape` records depth plus exact lexical scope
order, `StackDelta.apply?` rejects underflow without changing that scope order,
and successful enter, leave, and delta operations preserve
`StackShape.WellFormed`. ABI alignment and prologue selection remain parameters
consumed by later layers rather than choices made by this module.

`Grass.CFG.Call` makes each local or external call's complete outcome family
explicit. A well-formed call contract has a valid entry shape, distinct outcome
tags, and valid per-outcome stack shapes; a well-formed call site must reproduce
those tags in contract order and present the exact entry shape. Named projection
theorems expose each obligation without requiring downstream certificate code to
unfold the executable checks. ABI-specific outcome families and state predicates
remain provider inputs.

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
call-loan phases, and exact unwind correspondence. A literal call remains legal
and is checked against the same pre-call contract without implicit rewriting.

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
