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
