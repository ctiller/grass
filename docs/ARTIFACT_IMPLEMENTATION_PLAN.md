# Artifact, grammar, verified-object, and build implementation plan

Status: implementation plan owned by the `g-build` implementation agent. This
is a tier-four document under [README.md](README.md): it schedules work against
[GRAMMAR.md](GRAMMAR.md), [ARTIFACTS.md](ARTIFACTS.md),
[VERIFIED_OBJECTS.md](VERIFIED_OBJECTS.md), and
[OLEAN_SHARDING.md](OLEAN_SHARDING.md), and cannot weaken them.

## 0. Ownership and seams

`g-build` has exclusive implementation ownership of:

- `Grass/Grammar/**`: typed text/binary formats, derivations, streaming parser
  and writer laws;
- `Grass/Artifact/Binary/**`, `Grass/Artifact/COFF/**`, and
  `Grass/Artifact/PE/**`: concrete readers and writers realizing those formats;
- `Grass/Build/Cache/**` and `Grass/Build/Manifest/**`: semantic-environment
  Merkle keys, certificate replay, measured shards, and hierarchical manifests;
- the corresponding `Tests/Grammar/**`, `Tests/Artifact/**`, and
  `Tests/Build/**` fixtures; and
- this plan and [VERIFIED_OBJECTS.md](VERIFIED_OBJECTS.md).

[ARTIFACTS.md](ARTIFACTS.md), [GRAMMAR.md](GRAMMAR.md), and
[OLEAN_SHARDING.md](OLEAN_SHARDING.md) remain normatively owned by `g-design`.
This agent implements them. The sharding document constrains every workstream,
so this plan does not silently acquire authority to change another owner's
module layout. `lakefile.toml` and `.github/workflows/library.yml` are shared.

The subsystem boundaries are data-flow boundaries:

```text
g-construct raw layout/link descriptions
                 │
c-x86 encoding facts ──> generic Grammar algebra ──> COFF/PE/.gobj bytes
                 │                                  │
g-foundation Verify/Certificate gate ─────────────> manifest/link certificates
```

- **g-construct:** artifact writers consume raw layout/link descriptions, not
  high-level specifications. This plan does not invent a second layout model.
- **c-x86:** c-x86 owns every x86 encoding/decoding fact and its validation
  metadata. g-build owns the generic format algebra in which such facts may be
  stated. Agreement is required before moving or generalizing an instruction
  decoder; no opcode, prefix, operand, feature, or relocation fact belongs in
  `Grass.Grammar` merely because it is represented as bytes.
- **g-foundation:** `Grass/Verify/**` and `Grass/Certificate.lean` are consumed
  gates. `Build/Manifest` composes their values and does not redefine what a
  final certificate means.
- **g-design:** normative ambiguity is raised rather than resolved in this
  plan. In particular, implementation convenience cannot select ordered-choice
  semantics or weaken exact incomplete/invalid classification.

`VALIDATION.md` is intentionally unclaimed. Instruction/API campaigns and
unsafe-layer fuzzing remain cross-cutting work owned elsewhere.

## 1. Non-negotiable implementation invariants

1. Every writer has a reader for the same modeled format and an in-kernel
   value-level round-trip theorem on its writable domain.
2. Successful parsing returns the exact unconsumed suffix. Transport chunking
   may produce `needMore`; it may never manufacture `invalid`.
3. Parser completeness, incomplete-prefix exactness, and invalid-prefix
   exactness are separate obligations. Round-trip tests prove none of them.
4. Lengths, offsets, alignment, and addition are validated before indexing or
   allocation. No host wraparound is hidden behind a successful parse.
5. `.gobj` bytes contain a proof-free, first-order payload. They become usable
   by a verified link only through equality with the payload retained by the
   imported kernel certificate.
6. Cache hashes locate inputs; they never prove them. A replayed certificate is
   accepted only in the exact semantic environment named by its key.
7. A shard manifest measures what was rebuilt and why. No fixed-time or
   constant-time relinking claim is made without measurements.
8. Aggregate certificates have bounded fanout and mention child summaries, not
   flattened descendant instruction arrays.

## 2. Module architecture

The intended dependency direction is:

```text
Grammar/Core             ParseResult, Format, Derives
Grammar/Binary           endian integers, tags, padding, bounded lengths
Grammar/Streaming        chunk-invariant parser states and realization laws
       │
Artifact/Binary          concrete cursor and writer implementations
       ├─ Artifact/COFF       COFF structures and relocation container
       ├─ Artifact/PE         PE32+ image structures and loader-facing view
       └─ Artifact/Binary/Gobj proof-free verified-object payload format
                 │
Build/Cache              canonical semantic-environment Merkle keys
Build/Manifest           leaf/aggregate manifests and certificate DAG folds
```

The semantic result vocabulary lives in `Grammar/Core`; small total byte
consumers live in `Artifact/Binary/Primitive`, and their realization proofs in
`Artifact/Binary/Realization`. Later optimization can replace an executable
consumer while retaining `ParserRealizes`. Host `_root_.ByteArray` is used only
at an explicit adapter; format semantics use `Grass.Std.Logical.ByteArray`.

## 3. Milestones and exit gates

### G1 — generic grammar and streaming base

- Define typed `Format`, `Derives`, `ParseResult`, and stable error classes.
- Supply total one-byte and exact-length consumers with exact suffix laws.
- Add sequencing, choice without implicit priority, refinement, repetition
  progress, and length-prefix combinators.
- Prove parser/writer realization composition and rechunking invariance.
- Challenge empty input, every representative split, trailing suffixes,
  truncation, ambiguity, nullable repetition, and arithmetic bounds.

### G2 — `.gobj` and exact resolution

- Freeze a versioned, canonical first-order `GobjPayload` schema.
- Serialize `StableScopeId` as its two canonical UTF-8 components with
  unbounded self-delimiting lengths; never substitute a digest, UUID-sized
  token, dotted display rendering, or external registry handle for identity.
- Implement parser/writer laws and reject duplicate symbols, bad references,
  invalid permissions, noncanonical order, overflow, and trailing corruption.
- Connect successful parsing to structural well-formedness.
- Define resolution only by parsed-payload equality with the imported opaque
  object certificate; digests remain lookup evidence only.

### G3 — COFF and PE32+

- Model the required canonical COFF object/library and PE32+ subset.
- Cover headers, sections, symbols, imports/exports, relocations, alignment,
  padding, `.pdata`, and `.xdata` in parser/writer laws.
- Consume c-x86 relocation and instruction-byte facts behind an explicit
  interface; retain format/loader legality separation.
- Prove abstract loading establishes sections, relocations, imports, final
  permissions, unwind metadata, provenance, and entry transfer.

### G4 — verified objects and linker

- Implement stable public signatures with private object specifications.
- Check exact symbol/ABI/provider/resource/obligation composition and return
  precise link errors as data.
- Consume g-construct raw layouts and g-foundation certificate gates.
- Connect exact emitted bytes to the linked raw machine and thence to the
  retained precious root specification without vacuous load domains.

### G5 — cache and manifest locality

- Canonically hash source, imported summaries, semantic profiles, verifier,
  toolchain/options, and audit policy.
- Implement leaf and bounded-fanout aggregate manifests with explicit causes
  for hits, misses, and invalidations.
- Replay certificates only after exact environment reconstruction.
- Measure clean builds, body edits, interface edits, relocation-only edits,
  cache hits, proof bytes, peak memory, and rebuild cones.

## 4. Acceptance and verification

The default gate is `lake build`. Focused modules are checked first during
iteration, followed by `lake build` and the repository axiom audit before review.
Artifact fixtures are adversarial corpora, not the correctness argument. Each
milestone records the exact commands and product commit in the agent bus.

No implementation milestone is complete with a `sorry`, new axiom, unchecked
cast, native parser oracle, digest-as-proof shortcut, or an unmeasured locality
claim. `warningAsError` and the transitive axiom audit remain mandatory.

## 5. Bug inventory

The owned bug list contains no knowingly suppressed defect. Repaired findings
remain recorded below with their regression fixture and closure condition;
open design/dependency questions are tracked on the agent bus with a named
owner rather than disguised as implementation completion.

| Item | Kind | Owner | State | Closure |
|---|---|---|---|---|
| x86/grammar decoder seam | interface question | c-x86 + g-build | resolved (`c-x86:18`) | generic algebra stays here; x86 facts stay behind `Grass.ISA.X86`; error-algebra changes are coordinated |
| axiom-audit coverage import | shared integration | g-build, under `c-x86:13`/`:16` route | implemented; bus disposition awaits repair | `Tools/AxiomAudit.lean` imports `Grass.Grammar.Core`; 105-module audit passes |
| declaration-list coverage import | shared integration | g-build, under `c-x86:13`/`:16` route | implemented; bus disposition awaits repair | `Tools/DeclNames.lean` imports `Grass.Grammar.Core`; `DocstringAudit.py` passes |
| vacuous parser realization | implementation defect | g-build | repaired from `g-design:223` | `FormatSemantics.selectedComplete`, completion/invalid laws, and the four negative realizability fixtures prevent reject-all, subset, false-incomplete, and repairable-as-invalid parsers |
| diagnostic wording in precious semantics | implementation defect | g-build | repaired from `g-design:189` | `ParseError.class`, class-relative `ParserRealizes.invalidSound`/`invalidComplete`, two replacement-wording fixtures, and the wrong-class negative fixture |

When a defect is found, it is added here or linked to its bus issue before
unrelated feature work continues. A fixed row records its regression fixture
and verification command; it is not silently deleted.
