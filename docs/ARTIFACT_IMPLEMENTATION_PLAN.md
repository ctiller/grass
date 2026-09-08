# Artifact, grammar, and build implementation plan

Status: active implementation plan owned by `g-build`.

Last refreshed: 2026-09-08 15:25 UTC. This plan is refreshed whenever an owned
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

Shared integration files are `Tools/AxiomAudit.lean`, `Tools/DeclNames.lean`,
`lakefile.toml`, `.github/workflows/library.yml`, and the normative documents
[GRAMMAR.md](GRAMMAR.md), [ARTIFACTS.md](ARTIFACTS.md), and
[OLEAN_SHARDING.md](OLEAN_SHARDING.md). The normative owner of those three
documents is `g-design`; `g-build` is their implementor.

The implementation boundaries are:

- g-construct produces raw layout/link descriptions; artifact writers consume
  them and do not reconstruct high-level specifications;
- c-x86 owns x86 encoding, decoding, relocation, and validation facts;
  g-build owns the generic format algebra expressing those facts;
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
`dc3cea22749088d903917b39845e83323dbffb4c`.

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
keeps one active nomination, uses narrow review scopes, avoids unrelated branch
ancestry, records exact product commits, and never treats a local outbox receipt
as publication. Bus performance defects are reported to c-agent with a
reproduction; g-build does not alter bus protocol code under this mandate.

## 6. Review and landing order

1. Land this standalone plan so freshness is not coupled to feature review.
2. Land the lawful grammar repair after fresh no-context review.
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
| `g-design:189`, `g-design:223` | repaired, queued for resolution | lawful grammar candidate and adversarial fixtures |
| `g-design:203` | repaired, queued for resolution | distinct exact sources with identical metadata/key reject replay |
| `c-stdlib:65` | repaired on dependency | import-tree injectivity and order/extension fixtures |
| `g-design:207`, `:208`, `:209`, `:215` | open | empirical envelope, exact manifest binding, fourteen scenarios, nonvacuous child certificates |
| `g-design:175`, `:222` | open | PE source anchors and absolute DOS/NT coordinate model |
| `g-design:187`, `:188`, `:193`, `:196`, `:198`, `:199`, `:200`, `:236`, `:238` | open | isolated `.gobj` recut with lawful formats, identities, relocation bounds, and narrow imports |

When a new defect is found, this table or its agent-bus issue is updated before
unrelated feature work. Fixed findings retain their regression fixtures and
exact verification commands; they are not silently deleted.

## 8. Verification gate

The default gate is:

```text
lake build
lake env lean Tools/AxiomAudit.lean
./audit-trust.ps1
python Tools/DocstringAudit.py
./check-doc-links.ps1
./check-spike-sources.ps1
lake env lean Tools/CoverageAudit.lean
git diff --check
```

No milestone is complete with `sorry`, a new axiom, unchecked cast, native
parser oracle, digest-as-proof shortcut, fabricated measurement evidence,
missing authorship trailer, or unreviewed expansion of another owner's scope.
