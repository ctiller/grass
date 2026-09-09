# Contributing to Grass

Grass is currently an early foundation implementation plus specification
corpus. Contributions may extend the minimal compiling `Grass.*` foundation,
improve the reviewed architecture and proof-economics pressure tests, or improve
the validation tools around them. Most modules imported by `Spikes/` do not yet
exist; the spike files remain design fixtures, not a package that currently
builds.

Start with the [specification corpus index](docs/README.md), which defines
document authority and the meaning of normative language. For spike changes,
also read the [spike authoring contract](docs/SPIKE_AUTHORING.md) and compare
both the annotated document and its comment-free authored source.

## Making a change

The [endpoint index](docs/ENDPOINT_INDEX.md) helps locate code and its design
owner; the [validation command map](docs/CHECKS.md) explains check coverage.

1. Keep the precious portable specification minimal. Generated expansions,
   routine adapters, manifests, and bookkeeping do not belong in it.
2. Keep first-class assembly visible and authorable. Helpers may remove proof
   ceremony, but raw instructions and novel implementations must remain legal.
3. State new trust assumptions, external authorities, residual proof goals, and
   invalidation boundaries explicitly.
4. Cite primary vendor, standards-body, or research sources for externally
   defined behavior. Add reusable anchors to `docs/REFERENCES.md`.
5. Do not use `axiom`, `sorry`, `admit`, unsafe proof authority,
   `native_decide`, execution, tests, or digests as substitutes for universal
   proofs. Tests and fuzzers validate models; they do not prove them.
6. Keep caches, local worktrees, credentials, generated binaries, and editor
   state out of commits.
7. During review, ask whether each artifact can be produced deterministically
   by an algorithm. If it can, compute it; do not make an agent maintain a
   handwritten copy. Where intelligence is needed to choose an implementation
   or devise a proof, require an explicit deterministic check of that candidate
   against the specification. Identify any part that the check does not cover.

Run the repository's current consistency check from its root:

```bash
lake build
./audit-trust.sh
./check-source-input.sh
./check-spike-sources.sh
./check-doc-links.sh
```

The four checks require Bash and Perl. They run on Linux and in Git Bash on
Windows.

`audit-trust.sh` accepts repeated `--library-source-root`,
`--test-source-root`, `--declaration`, and `--allowed-axiom` options when a
focused audit needs to replace one of its default lists.

`lake build` compiles both `Grass` and `Tests`, the default targets in
`lakefile.toml`. Use `lake build Tests` for a focused test-library build rather
than repeating it after an unchanged default build. The trust command audits
project declarations and named public roots for rejected transitive axioms, then
rejects unverified `implemented_by` and `extern` replacements in the verified
runtime dependency closure. Participating module cohorts and persisted non-meta
compiler dependency modules keep scoped `csimp` substitutions covered after
their attribute state expires.
The last two commands classify spike code, compare authored blocks with their
files under `Spikes/`, and check relative documentation targets. None of these
commands is an end-to-end proof of the eventual assembler or executable.

## Review

Every product change receives independent peer review of the actual diff and
relevant surrounding code. The author may commit and push a reviewed checkpoint;
there is no bus registration, nomination, role assignment, or reviewer-owned
merge requirement. Review findings and checks are recorded with the checkpoint
or pull request. Unresolved findings block acceptance. Reviewers run risk-proportionate checks
on the reviewed candidate and report exact commands and results. A reviewer who
authors material fixes needs another independent reviewer for those fixes. Use
fresh reviewer contexts at major boundaries so inherited assumptions receive
another independent look. Never force-push shared branches.

Reviewers apply [the substantive review standard](docs/REVIEW.md), challenging
specification adequacy, proof feasibility, proof economics, assembly freedom,
change blast radius, source authority, and fitness for the implementation brief.

## Shared guarantees and second consumers

Accepted architecture delivery guidance, approved by Craig and reported by
architecture on 2026-09-09. Every shared guarantee has an owner. Before
implementation, separate the domain-specific obligations from mechanical
checked construction and general laws. At the **second consumer**, reuse the
existing implementation or extract shared construction/laws. A new consumer
uses that shared implementation unless architecture approves separate treatment
with a concrete reason. Review asks what a
**third consumer** would still need to prove.

Architecture owns this rule and its exceptions; library owns shared laws,
specialists integrate their consumers, and the auditor compares new consumers
with existing ones during bounded audits. An exception record needs only the
guarantee, owner, consumers, concrete reason for separate treatment, and revisit
trigger. Record it with the owning design or reviewed change rather than adding
a separate coordination system.

Shared implementation and actual adoption are delivery criteria, not optional
cleanup: duplication must be controlled to preserve forward progress.
Reuse closure requires existing consumers to use the shared construction/laws,
preserving exact indices, refusal behavior and guarantees, with appropriate
focused checks. A common type alone, generated copies of proof scripts,
similar-looking code or a lower line count does not prove closure. Remove the
old duplicate implementations once both consumers adopt the shared one;
compatibility aliases may remain. An approved exception records the distinct obligation rather than
claiming shared reuse has been completed.

This is not a mandate for speculative abstraction or an automatic cleanup
campaign. Spikes sequences work, and the unchanged authored
`Program → helloVerified → emitProgram` chain remains the priority.

### Proposed evaluation: instruction and API declarations

Craig proposes evaluating instruction/API DSLs as a possible way to express
the distinction above. This is an evaluation idea, not an implementation mandate
or a new project. Existing semantic structures remain authoritative. Declarations
would supply the distinct encoding, operands, effects, access and fault
obligations for instructions, or ABI, request, loan and outcome obligations for
APIs; shared verified elaborators or constructors would prove common mechanics
once. Generating copies of proof scripts alone would not achieve that reuse.

Any evaluation preserves first-class authored assembly and custom implementations;
instruction and API vocabularies may stay separate. Compare two meaningfully
different instructions and two APIs, then ask what a third consumer must author.
Judge proof burden, retained guarantees and expressiveness, not line count.
Spikes sequences any evaluation; this note starts no automatic DSL build.
The ReturnHome dual-consumer extraction is a concrete case study for that
evaluation, not evidence by itself that a DSL would help.

### Initial bounded trial

The already accepted ReturnHome trial requires **both GetStdHandle and WriteFile**
to consume the canonical producer, loan pair and frame projection in the same
change. Publishing a common type is insufficient; one consumer now and a second
independent producer pending later cleanup do not satisfy it. Supplier
implementation is still pending. The API-specific obligations remain separate.

Architecture's next raw-entry work uses or factors shared checked-handoff and
log laws rather than adding per-API copies. This is bounded work within spikes'
sequence, not a blanket rewrite of existing implementations.

The auditor's *Cross-consumer duplication sweep*, pinned to `2370d929`, reports
seven **additional evidenced families**, excluding that ReturnHome trial. This
is a lower bound, not an exhaustive census. It alleges no wrong output and
reports no measured savings. The following is a compact projection of that
report; links are navigation into the checkout, while the evidence belongs to
the pinned revision (use `git show 2370d929:<path>` for that source).

| Finding | Shared mechanism to assess | Starting consumer locations |
|---|---|---|
| DUP-01 | Checked API entry handoff and preservation | [WriteFileHandoff](Grass/Platform/Win32/WriteFileHandoff.lean), [GetStdHandleRuntime](Grass/Platform/Win32/GetStdHandleRuntime.lean), [ExitProcessRuntime](Grass/Platform/Win32/ExitProcessRuntime.lean) |
| DUP-02 | Width-indexed completed-read construction and laws | [ReadValue32](Grass/ISA/X86/Execution/ReadValue32.lean), [ReadValue64](Grass/ISA/X86/Execution/ReadValue64.lean) |
| DUP-03 | All-or-none list traversal, order and successful-element provenance | [SourceInitialization](Grass/Assembly/SourceInitialization.lean), [SourceImportRequests](Grass/Assembly/SourceImportRequests.lean), [SourceImportBindings](Grass/Assembly/SourceImportBindings.lean), [PE Exceptions](Grass/Artifact/PE/Exceptions.lean) |
| DUP-04 | Counted parser/writer recovery with exact suffix | [ImageReader](Grass/Artifact/PE/ImageReader.lean), [ExceptionReader](Grass/Artifact/PE/ExceptionReader.lean) |
| DUP-05 | Access-free execution receipt construction | [BodyComputationFactory](Grass/ISA/X86/Execution/BodyComputationFactory.lean), [ComputationFactory](Grass/ISA/X86/Execution/ComputationFactory.lean) |
| DUP-06 | Access-failure mapping that retains the actual reached state | [PushFactory](Grass/ISA/X86/Execution/PushFactory.lean), [CallFactory](Grass/ISA/X86/Execution/CallFactory.lean), [MemoryMoveFactory](Grass/ISA/X86/Execution/MemoryMoveFactory.lean), [ReturnSlotFactory](Grass/ISA/X86/Execution/ReturnSlotFactory.lean), [FetchFactory](Grass/ISA/X86/Execution/FetchFactory.lean) |
| DUP-07 | Placement recovery indexed by the same successful access run and address plan | [PushFactory](Grass/ISA/X86/Execution/PushFactory.lean), [CallFactory](Grass/ISA/X86/Execution/CallFactory.lean), [MemoryMoveFactory](Grass/ISA/X86/Execution/MemoryMoveFactory.lean), [ReturnSlotFactory](Grass/ISA/X86/Execution/ReturnSlotFactory.lean) |

Library read-only triage has been requested; implementation of these seven
candidates awaits spikes' sequencing. Four are substantial proof/construction
families and three are smaller helpers. The report's speculative FrameLoad/
FrameLea and StaticSectionPacking candidates are excluded from the count, as are
already-shared runtime table updates and superficially similar domain laws.

## Spike-first rebuild workflow

Complete Hello World, sort, gzip, HTTP/2 server, then spinning cube, in order.
Hold each existing spike's behavior and authored source steady except for a
demonstrated defect or an implementation approach that proves unreasonable.
Record the reason for such changes and retain the annotated/source mirror.
Internal library interfaces may change to meet that acceptance surface.

As completed spike work reveals better abstractions, assign bounded rewrite
agents to rebuild earlier implementation around them. Keep the main effort
advancing the spikes. Each rewrite names its consumers, preserves the authored
specification and required public laws, and passes deterministic checks and
independent review before integration. For repeated populations, prefer a shared
Lean description with general proofs over separately maintained instances.

Work through the active spike's complete specification-to-artifact chain. Add or
refine library code when that chain needs it; do not build independent layers
merely to satisfy a speculative roadmap. A compiling fixture or runnable binary
alone does not finish a spike: its acceptance document and implementation ratchet
require the connected proofs, exact bytes, failure cases, and rebuild evidence.

Preserve existing agent branches as spare parts. Mine selected code from them and
from predecessor projects, checking its theorem strength, dependencies, and exact
source connections before reuse. No bulk merge is implied by a useful fragment.
Historical plan section numbers and bus event IDs in implementation comments are
provenance available in Git history, not current authority or work assignments.
New guidance belongs with its narrow owning design document.

Publish reviewed, validated checkpoints to GitHub during development. Keep the
current spike's remaining obligations concrete and small; do not recreate the
retired coordination system or per-layer implementation plans.

Do not include confidential vulnerability details in an ordinary issue or
review. Follow [SECURITY.md](SECURITY.md) instead.

All project participation is governed by
[the code of conduct](CODE_OF_CONDUCT.md).

## Contribution licensing

Unless explicitly marked otherwise, a contribution intentionally submitted for
inclusion in Grass is provided under the
[Apache License, Version 2.0](LICENSE), as described by section 5 of that
license. Do not submit material that you do not have the right to contribute.
