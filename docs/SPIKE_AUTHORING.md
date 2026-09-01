# Spike authoring and review contract

## Purpose

Grass spikes have two views with different jobs. The paired `docs/SPIKE_N.md`
is the annotated design and expansion. `Spikes/N_Name/` is the Lean source an
agent is expected to author and maintain. Reviewers must compare them. Neither
view may be used to hide cost or correctness obligations present in the other.

## The authored directory

Every `.lean` file under `Spikes/N_Name/` counts as program-author ceremony.
It contains the source we expect a capable Grass authoring agent to type,
review, revise, and keep under version control. It is not a dumping ground for
generated manifests or for one file per internal proof-record field.

The authored source includes:

- the precious specification;
- genuinely selected resource and platform policy;
- a nonstandard process presentation when the program genuinely benefits from
  one;
- first-class assembly, shader, or other machine source;
- novel model, layout, constructor, and connection theorems the libraries
  cannot derive generically; and
- the final verified-program construction and emission request.

The authored source normally omits:

- source-closure and import manifests derivable from the typed source AST;
- label-to-cancellation dictionaries derivable from block annotations;
- ordinary ABI, frame, relocation, writer/parser, and artifact bundle records;
- the generated internal network of a standard sequential adapter;
- duplicate `rfl` projections of data already owned by another term; and
- files whose only purpose is to pass one unchanged value to the next theorem.

Omission from the authored directory does not remove a proof demand. The
library elaborator must construct a checked certificate, expose failures at a
named boundary, and make the derived value inspectable.

Physical module boundaries are permitted when they bank a meaningful reusable
proof, isolate an independently changing subsystem, or keep a large source
legible. They require an explanation in the annotated document. A small
program is not forced into the module shape of a server or game engine.

## The annotated spike document

`docs/SPIKE_N.md` contains the information needed to judge the proposal before
the supporting libraries exist. It includes:

1. the exact authored Lean source, by file;
2. prose explaining the precious behavior and every intentional policy;
3. the important generated elaborations, manifests, process plans, CFG
   contracts, proof junctions, artifact structures, and residual goals;
4. the raw or sufficiently exact expanded instruction view needed to establish
   that macros and constructors do not hide the program;
5. believable proof sketches for generic theorems on which the concise source
   relies;
6. failure, fault, cancellation, resource, and progress cases;
7. the expected invalidation cone for representative changes; and
8. mutation and negative fixtures that make the proposed automation
   falsifiable.

Generated material in the document is explanatory and reviewable, but does not
become authored ceremony merely because the pre-implementation spike writes it
out. It still counts toward elaboration, kernel checking, generated artifact
size, and build-performance measurements.

Every fenced code block must be preceded immediately by one machine-readable
classification line:

<!-- grass-block: interface id=block-classification-syntax -->
```text
<!-- grass-block: authored file=Spec.lean -->
<!-- grass-block: generated id=expanded-x86 derives=Program.lean:helloSource -->
<!-- grass-block: interface id=verified-fragment -->
<!-- grass-block: proof-sketch id=macro-expansion-exact -->
```

The four classes are:

- **authored source** — appears exactly in the spike directory;
- **generated expansion** — deterministically produced from authored source;
- **library interface sketch** — a demanded supporting interface, not
  application code; or
- **proof sketch** — an argument that must eventually become a checked library
  theorem or spike proof.

Identifiers are unique within a document. An authored block names its normalized
relative path. A generated block names the authored declaration(s) and checked
constructor(s) from which it derives. An interface or proof-sketch block names
the residual library obligation it creates. Unknown, duplicate, or unlabeled
blocks fail review; blanket prose covering several blocks is not a label.

## How authored source expands

Expansion is one deterministic, inspectable pipeline. It is not permission for
an elaborator or tactic to invent invariants, choose policies, or synthesize an
implementation which the authored source did not select.

<!-- grass-block: interface id=expansion-pipeline -->
```text
Spikes/N_Name/*.lean
  | parse and elaborate ordinary Lean/Grass syntax
  v
typed specification + typed realization source
  | expand only named library constructors and macros
  v
process presentation + CFG + raw instruction/shader streams
  | derive structural evidence
  v
source closure + ABI/cancellation maps + relocation/import manifests
  | run checked local and compositional proof procedures
  v
machine certificate + residual goals
  | serialize and link using proved writers
  v
VerifiedProgram spec + emitted artifact
```

At every arrow the annotated document must show either the exact output or a
compact digest plus an exact, reproducible command for obtaining the full
output. A digest is insufficient for the final raw instruction/shader stream,
residual goals, imported authority, or emitted-section layout: those must be
available in full to adversarial review even when they are too large for the
main narrative.

Each phase has a closed authority boundary:

- parsing may resolve syntax and types, but may not choose behavior;
- constructor and macro expansion may instantiate a named proved schema, but
  may not discover a loop invariant or silently change an algorithm;
- structural derivation may collect facts already present in typed terms, but
  may not discharge a novel semantic obligation;
- proof automation may consume declared contracts and produce checked proof
  terms, but must report every residual goal and the theorem/certificate used
  at each closed goal; and
- serialization may choose only representation details permitted by the
  selected artifact policy and must retain its round-trip and parser laws.

If a phase needs a choice outside that boundary, the choice moves upward into
the authored directory. If a repeated authored choice becomes a proved,
parameterized library constructor, a later spike may move it into generated
expansion and must name that constructor explicitly.

The generated expansion is never edited in place. Regeneration from the exact
authored source must reproduce it byte-for-byte modulo fields explicitly
classified as nondeterministic build metadata; verified artifacts should avoid
such fields or normalize them before comparison.

## Exact cross-view laws

For each spike, the corpus owes an `AuthoredSpikeManifest` derived recursively
from the directory and an `AnnotatedSpikeManifest` extracted from every labeled
block in the document. Source text is compared after UTF-8 decoding, CRLF/CR to
LF normalization, and removal of trailing line terminators; paths use `/` and
remain case-sensitive. Review requires separate laws for separate phases:

<!-- grass-block: interface id=cross-view-laws -->
```lean
theorem annotated_authored_source_exact :
  annotated.authoredFiles = directory.authoredFiles

theorem typed_source_closure_exact :
  typecheck environment directory.authoredFiles = .ok annotated.typedSource

theorem constructor_expansion_exact :
  expand environment annotated.typedSource = .ok annotated.expandedSource

theorem process_cfg_extraction_exact :
  extract environment annotated.expandedSource = .ok annotated.processCfg

theorem machine_manifest_exact :
  manifest environment annotated.processCfg = .ok annotated.machineManifest

theorem residual_goal_report_exact :
  check environment annotated.machineManifest = annotated.proofReport

theorem emitted_artifact_exact :
  write environment annotated.machineManifest = .ok annotated.artifact

theorem generated_evidence_not_authored :
  Disjoint directory.authoredFiles annotated.generatedOnlyFiles

theorem every_concise_step_has_authority :
  EveryGeneratedClaimNamesCheckedLibraryTheoremOrResidualGoal annotated
```

`environment` closes over exact Grass/library declaration identities and
normalized theorem types, registry versions, Lean/toolchain/options, selected
profiles and policies, macro hygiene, canonical ordering, encoder and
branch-relaxation policy, and serializer version. Proof terms need not be
byte-stable, but their theorem types and kernel-check results do. Any permitted
nondeterministic build metadata has an explicit whitelist and normalization
theorem.

Before the library exists, the expansion laws are review obligations.
`./check-spike-sources.ps1` currently proves only the normalized authored-source
snapshot equality; it must never be cited as evidence for expansion,
certificate, or artifact reproducibility. The script accepts `-Spike N` for a
focused check. Once implementation begins, CI also runs clean-output generation
and enforces every phase independently.

### Pre-implementation design fixpoint

The present corpus is explicitly forbidden from building the supporting
library. Its design fixpoint therefore does not require fabricated generator
output, proof terms, timings, executable mutations, or synthetic scale runs. It
does require:

- exact classified authored source;
- a total interface and believable proof sketch for every unavailable phase;
- no hidden invariant discovery, policy choice, semantic correspondence, or
  source input in a purportedly derived step;
- every unavailable result recorded as `not generated` or `not measured`; and
- an explicit implementation ratchet naming the future command, output schema,
  mutation fixture, and acceptance criterion.

A handwritten listing may be a proof sketch but cannot be called generated or
exact evidence. Design approval means the demanded libraries can be built
without choosing another foundational interface; it does not mean the program
has compiled or the artifact exists. Actual expansion, kernel replay, artifact
reproduction, mutations, and the structural/graph/measured locality ratchet in
[OLEAN_SHARDING.md](OLEAN_SHARDING.md) are blocking gates for implementation
acceptance, not for this document-only fixpoint.

## Proof-economics accounting

Reviews report at least four separate quantities:

1. authored specification lines and modules;
2. authored realization/assembly lines and modules;
3. generated source/certificate/proof-term size; and
4. clean and incremental elaboration/kernel-check cost.

Each spike uses one standard accounting table, including physical and nonblank
authored lines by class, authored module count, generated bytes/nodes/goals and
proof-term size, clean check time, and representative incremental check time.
Until the relevant library or generator exists, the entry is literally `not
generated` or `not measured`; absence is not evidence of low cost. Each authored
module has a one-sentence justification as an abstraction or build boundary.

No one of these substitutes for another. A one-line command backed by a huge
generated proof may have good author economics and bad build economics. Eleven
tiny hand-maintained pass-through files have bad author economics even if their
proof terms are cheap. A concise DSL which hides an unresolved semantic choice
has neither.

Line ratios remain smell tests, never machine-enforced product requirements.

## Mandatory adversarial cross-check

Every external and smeller review must answer:

1. Does every block labeled authored appear in the directory exactly, and is
   every directory file represented in the document?
2. Is any generated manifest, binding, packaging theorem, or adapter witness
   being charged to the author unnecessarily?
3. Is any genuinely novel semantic choice being mislabeled as generated?
4. Can the claimed generated expansion actually be derived from the displayed
   source without invariant discovery, policy choice, or missing code?
5. Does changing one representative spec clause, assembly block, placement, or
   platform choice produce the documented invalidation cone?
6. Is the file count proportionate to authored abstractions, or merely to the
   number of internal theorem stages?
7. Starting from a clean generated-output directory, does the documented
   expansion command reproduce every reviewed process, CFG, instruction,
   certificate, import, relocation, and artifact-layout view?
8. At which exact phase would a changed specification clause first fail, and
   does that failure occur before any stale downstream evidence can be reused?

A review which examines only the document or only the directory is incomplete.

## Initial module expectations

Hello World uses two authored files: `Spec.lean` and `Program.lean`. Sort and
gzip begin with `Spec.lean`, `Assembly.lean`, and `Program.lean`; a reusable
kernel may earn a separate module when it is genuinely shared or independently
verified. The HTTP/2 server and cube may use more modules for their explicit
process models and independently tuned machine subsystems, but generated source
closure, cancellation maps, and artifact wrappers do not earn authored files.

These counts are baselines for review, not permanent caps. The governing rule
is that the directory models what agents actually maintain.
