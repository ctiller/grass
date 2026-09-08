# Artifact, grammar, and build implementation plan

Status: active implementation plan owned by `g-build`.

Last refreshed: 2026-09-08 22:20 UTC. This plan is refreshed whenever an owned
milestone, finding disposition, dependency, or review state changes, and at
least once within every twelve-hour active-work interval.

This tier-four plan schedules implementation against [GRAMMAR.md](GRAMMAR.md),
[ARTIFACTS.md](ARTIFACTS.md), [VERIFIED_OBJECTS.md](VERIFIED_OBJECTS.md), and
[OLEAN_SHARDING.md](OLEAN_SHARDING.md). It cannot weaken those normative texts.

## 1. Ownership and seams

`g-build` exclusively implements:

- `Grass/Grammar/**` and `Tests/Grammar/**`;
- `Grass/Artifact/Binary/**`, `Grass/Artifact/COFF/**`,
  `Grass/Artifact/PE/**`, and `Tests/Artifact/**`;
- `Grass/Build/Cache/**`, `Grass/Build/Manifest/**`, and `Tests/Build/**`;
- `Grass/Emit.lean`, this plan, and [VERIFIED_OBJECTS.md](VERIFIED_OBJECTS.md).

Shared integration files are `lakefile.toml`, `.github/workflows/library.yml`,
and the normative documents
[GRAMMAR.md](GRAMMAR.md), [ARTIFACTS.md](ARTIFACTS.md), and
[OLEAN_SHARDING.md](OLEAN_SHARDING.md). The normative owner of those three
documents is `g-design`; `g-build` is their implementor.

The implementation boundaries are:

- g-construct produces raw layout/link descriptions; artifact writers consume
  them and do not reconstruct high-level specifications;
- c-x86 owns x86 encoding, decoding, relocation, and validation facts;
  g-build owns the generic format algebra and the COFF/PE container formats
  expressing those facts. `g-build:173` freezes the duplicate
  `Grass/Platform/Win32/Coff*` and `Pe*` container surface while the two owners
  agree narrow adapters; c-x86's executable-image and processor-probe callers
  remain consumers of the artifact writer;
- g-foundation owns `Grass/Verify/**` and `Grass/Certificate.lean`;
  Build/Manifest consumes those gates without redefining them; and
- c-agent owns agent-bus implementation. This plan covers g-build's use of bus
  receipts and its measured build/review latency, not changes to bus semantics.

`VALIDATION.md` remains unassigned and cross-cutting.

## 2. Non-negotiable invariants

1. Every writer has a reader for the same modeled format and an in-kernel
   round-trip theorem on its writable domain.
2. Parser realization is nonvacuous: an explicit selection policy covers every
   recognized input, incomplete prefixes have finite completions, invalid
   prefixes have none, and diagnostic wording is not precious by default.
3. Successful parsing preserves the exact suffix. Lengths, offsets, alignment,
   and addition are checked before indexing or allocation.
4. `.gobj` is proof-free data. It becomes certificate-usable only after parsing
   the exact canonical payload retained by the imported kernel certificate.
5. Stable scope identity, imported-callable identity, relocation ISA/profile,
   and section bounds survive serialization without opaque substitutes.
6. Hashes locate cache candidates; they never authorize proof transport.
   Certificates remain indexed by exact source/import/profile values.
7. A measured manifest names its exact Git tree, command/tool environment,
   mutation, before/after roots, raw evidence identities, and observation
   source. Structural consistency alone is not called measurement evidence.
8. Aggregate certificates have bounded fanout and consume the exact concrete
   child manifests/certificates they summarize.
9. PE file offsets use one checked absolute coordinate system rooted through
   the DOS header and `e_lfanew`; fragment-local readers are named as fragments.
10. Every changed declaration is covered by build, axiom, trust, documentation,
    link, source, coverage, authorship-trailer, and review-scope gates.

## 3. Work lanes

### G1 — lawful generic grammar

- Maintain typed `Format`/`Derives`, explicit selection policies, exact
  success/incomplete/invalid laws, and stable `ParseErrorClass` projection.
- Add sequencing, choice, refinement, repetition progress, length-prefix,
  endian, tag, padding, and bounded-length combinators.
- Require adversarial fixtures for reject-all/subset parsers, false `needMore`,
  repairable-as-invalid, wrong error class, ambiguity, and every input split.

Current repair candidate: `agent/g-build/grammar-lawful-semantics` at
`65c7d9b268bd3b526fd3c605b47dc04604564860`, nominated as `g-build:159`.

### G2 — `.gobj` and exact resolution

- Recut `.gobj` directly on the smallest reviewed binary-format base, without
  inheriting unrelated PE/COFF history.
- Serialize canonical hierarchical `StableScopeId` values, imported callable
  targets, and relocation ISA/profile identity.
- Give envelope and every table an independent `Format`, `ParserRealizes`, and
  `WriterRealizes` proof with arbitrary-input and split-prefix fixtures.
- Parse entries incrementally so early invalid fields outrank missing later
  bytes and every numeric deficit is a true minimum.
- Keep exact payload equality in a narrow resolution module; structural table
  validation is a separate consumer.

### G3 — COFF and PE32+

- Recut authenticated, bounded COFF and PE slices from current reviewed bases.
- Anchor modeled vendor layouts to stable Microsoft PE/COFF table locators and
  distinguish vendor facts from Grass canonical-subset choices.
- Coordinate duplicate COFF concepts and relocation facts with c-x86.
- Model DOS header/stub, `e_lfanew`, NT headers, section table, raw/file-only
  regions, imports/exports, base relocations, `.pdata`, and `.xdata` in one
  overflow-checked absolute file coordinate system.
- Prove parser/writer laws, structural legality, abstract loading, final
  permissions, unwind metadata, provenance, and entry transfer separately.

### G4 — verified objects and linker

- Implement stable exported signatures with private exact object
  specifications and hierarchical source ownership.
- Consume g-construct raw descriptions and g-foundation certificates.
- Check exact symbols, imports, ABI/provider/resource/obligation composition,
  relocation ranges, section permissions, and root selection.
- Return link failures as precise data and connect emitted bytes to the retained
  precious root specification.

### G5 — cache and manifest locality

- Keep `SemanticEnvironmentMetadata` digest-only and lookup-only; retain an
  arbitrary exact environment beside every certificate.
- Prove ordered import preimage injectivity before hashing and scan colliding
  candidates by exact environment equality.
- Bind every manifest DAG node to one exact leaf/aggregate value and bind every
  child summary to the concrete child identity and exported summary.
- Separate structural campaign consistency from empirical `EvidenceEnvelope`
  admission, deriving changes from retained before/after inputs.
- Cover all fourteen normative locality scenarios, including aggregate
  rebalance and the five process-sharding edit classes.

Current cache repair candidates:

- exact proof indices: `agent/g-build/cache-exact-proof-index` at
  `1ed72f7b5a4c7ac4baa70948b70745182dc2f65e`;
- import preimage injectivity: `agent/g-build/cache-import-tree-injective` at
  `a1eeacd90a66b833840a81e5505953608aafb9d9`, stacked on c-stdlib's
  `Vec.foldr_cons` dependency.

## 4. Artifact hashing and evidence

Cache keys use domain-separated canonical Merkle preimages for source metadata,
ordered imported summaries, semantic profile, verifier, toolchain, generator,
options, and audit policy. The lookup record retains that full preimage. A
separate exact value—potentially containing source terms, public summaries, or
kernel-owned declarations—indexes the certificate. Equality of digests or
metadata projections cannot cast the certificate.

Artifact reuse additionally parses the candidate bytes and proves equality to
the exact payload owned by its certificate. Manifest roots and artifact hashes
remain mismatch detectors and content addresses, never substitutes for those
equalities.

## 5. Build and agent-bus performance

The build ratchet records cold/no-op runs, leaf edits, interface edits,
relocation/layout edits, aggregate rebalance, cache hits, and all process-shard
edit classes. Reports include elapsed time, peak memory, checked declarations,
`.olean`/proof/artifact bytes, affected nodes, and exact evidence identities.
No constant-time or asymptotic claim is made from caller-authored numbers.

Agent-bus integration is measured from local submission to coordinator
publication, reviewer acceptance, authorization, and merge receipt. g-build
keeps independent bounded nominations in parallel, uses narrow review scopes,
avoids unrelated branch ancestry, records exact product commits, and never
treats a local outbox receipt as publication. Dependent stacks remain ordered
behind their reviewed prerequisites rather than being presented as one giant
candidate. Bus performance defects are reported to c-agent with a reproduction;
g-build does not alter bus protocol code under this mandate.

## 6. Review and landing order

1. Land this standalone plan through e-reviewer so freshness is not coupled to
   feature review, in parallel with the Grammar review.
2. Land the lawful grammar repair through c-reviewer after fresh no-context
   review.
3. Land c-stdlib's fold laws, then the dependent cache import-preimage proof.
4. Land the exact-index cache repair after reconciling its refreshed key base.
5. Repair and nominate manifest evidence/scenario/certificate slices in
   dependency order.
6. Recut `.gobj`, COFF, and PE into narrow authenticated branches; do not
   nominate the existing moving artifact stacks.

Each nomination requires the exact-tip build and audit suite, a complete
`origin/main..tip` trailer audit, and a review scope equal to every changed
path. Findings are fixed or explicitly rejected with normative evidence before
unrelated feature work resumes.

## 7. Bug inventory

No known defect is silently suppressed. Current findings are the work queue:

| Findings | State | Closure evidence |
|---|---|---|
| `e-auditor:29`, `e-auditor:35` | open until this plan lands | standalone reviewed plan on `main`; current bus plan is `g-build:174` |
| `g-design:175`, `g-design:222` | open | PE source anchors and absolute DOS/NT coordinate model |
| `g-design:188` | open | independent `.gobj` `Format`, `ParserRealizes`, and `WriterRealizes` proofs with arbitrary-input fixtures |
| `g-design:196` | partially repaired, still open | isolated `.gobj` recut exists at `2173284b59721f2d3559244d22600a54e79fc8d2`; Grammar must land and the remaining PE/COFF ancestry must be recut |
| `g-build:173` | awaiting c-x86 | migrate container formats to `Artifact/COFF` and `Artifact/PE`; retain x86/Windows facts and executable consumers behind typed adapters |
| `g-design:187`, `g-design:198` | resolved as `g-build:155`, `g-build:156` | canonical structured `StableScopeId` framing, recovery, injectivity, and collision fixtures |

When a new defect is found, this table or its agent-bus issue is updated before
unrelated feature work. Fixed findings retain their regression fixtures and
exact verification commands; they are not silently deleted.

## 8. Verification gate

The default gate is:

```text
lake build
lake env lean Tools/AxiomAudit.lean
./audit-trust.ps1
cargo fmt --manifest-path tools/grass-tools/Cargo.toml --all -- --check
cargo clippy --locked --all-targets --manifest-path tools/grass-tools/Cargo.toml -- -D warnings
cargo test --locked --manifest-path tools/grass-tools/Cargo.toml
cargo build --release --locked --manifest-path tools/grass-tools/Cargo.toml
./tools/grass-tools/target/release/docstring-audit
./tools/grass-tools/target/release/coverage-audit
./check-doc-links.ps1
./check-spike-sources.ps1
git diff --check
```

`Tools/AxiomAudit.lean` is retained above only while the repository workflow
still names that compatibility entry point. New Grammar and artifact modules
must use the owner-authored dynamic audit once that migration lands; this plan
does not restore or extend a hand-maintained Lean module registry.

No milestone is complete with `sorry`, a new axiom, unchecked cast, native
parser oracle, digest-as-proof shortcut, fabricated measurement evidence,
missing authorship trailer, or unreviewed expansion of another owner's scope.
