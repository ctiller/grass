# Grass specification corpus

Status: pre-implementation normative design, ready for adversarial review.

This corpus defines the interfaces and proof demands that implementation must
meet. A later implementation may reveal that an interface is inconvenient; it
may not silently weaken a demand. Changes to a normative demand require an
explicit decision record and renewed review of affected documents.

## Authority

When documents conflict, authority is:

1. [FOUNDATION.md](FOUNDATION.md) for scope, trust, and non-negotiable laws.
2. The narrowly owning normative document listed below.
3. [DECISIONS.md](DECISIONS.md) for ratified interpretations not yet folded in.
4. Plans, examples, and implementation notes.

No document may override a narrower owner by restating it differently.

## Normative owners

| Document | Owns |
|---|---|
| [VISION.md](VISION.md) | large-system target, proof-economy priorities, spike interpretation |
| [FOUNDATION.md](FOUNDATION.md) | mission, trust boundary, repository laws |
| [SEMANTICS.md](SEMANTICS.md) | executions, nondeterminism, observations, safety, progress, liveness |
| [SPECIFICATION_LANGUAGES.md](SPECIFICATION_LANGUAGES.md) | open family of precious DSL fragments and their typed semantic junctions |
| [GRAMMAR.md](GRAMMAR.md) | precious text/binary languages, incomplete versus invalid prefixes, parser/writer realization laws |
| [PROCESS.md](PROCESS.md) | portable state/event/demand/view processes, networks, channels, flattening, resources, and driver boundary |
| [VERIFIED_PROGRAM.md](VERIFIED_PROGRAM.md) | the public certificate and emission gate |
| [MEMORY_MODEL.md](MEMORY_MODEL.md) | memory, provenance, borrowing, concurrency, faults |
| [OBLIGATIONS.md](OBLIGATIONS.md) | linear obligations, transfer, exit dispositions |
| [REFINEMENT.md](REFINEMENT.md) | refinement proof concerns, weaving, provider realization, generated/authored machine routes |
| [ASSEMBLY_CONSTRUCTION.md](ASSEMBLY_CONSTRUCTION.md) | typed layouts, physical placement, verified generated instruction fragments, literal escape |
| [INSTRUCTIONS.md](INSTRUCTIONS.md) | extensible operations, ghost erasure, raw instructions, ISA profiles |
| [PLATFORM_ABI.md](PLATFORM_ABI.md) | platform plans, APIs, ABIs, Win32 x64 baseline |
| [ARTIFACTS.md](ARTIFACTS.md) | parsers, writers, PE/COFF, relocation, connection theorems |
| [VALIDATION.md](VALIDATION.md) | citations, probes, fuzzers, TCB ledgers, CI gates |
| [STDLIB.md](STDLIB.md) | fundamental data structures and reusable proof laws |

## Review and delivery

- [VISION.md](VISION.md) explains the large-system objective and the tradeoffs
  against which spike proof economy is judged.
- [PROOF_FEASIBILITY.md](PROOF_FEASIBILITY.md) gives constructive proof sketches,
  automation limits, falsification fixtures, and fallbacks for mechanisms
  challenged as implausible.
- [HELLO_WORLD.md](HELLO_WORLD.md) defines the first acceptance milestone.
- [SPIKE_1.md](SPIKE_1.md) is its annotated proof from portable specification to
  emitted Win32 PE bytes.
- [SORT.md](SORT.md) defines the second acceptance milestone.
- [SPIKE_2.md](SPIKE_2.md) is the annotated proof proposal for an in-memory stable,
  allocation-aware stdin byte-line sort.
- [GZIP.md](GZIP.md) and [SPIKE_3.md](SPIKE_3.md) define and fully lower the
  bounded-memory streaming gzip milestone.
- [WEB_SERVER.md](WEB_SERVER.md) and [SPIKE_4.md](SPIKE_4.md) define and fully
  lower the cancellable multiplexed in-memory cleartext HTTP/2 server milestone.
- [CUBE.md](CUBE.md) and [SPIKE_5.md](SPIKE_5.md) define and fully lower the
  Win32/Vulkan/SPIR-V spinning-cube composition milestone.
- [../Spikes/README.md](../Spikes/README.md) indexes the matching comment-free
  expected Lean source files, including final PE emission and connection
  theorems. They are design fixtures until the Grass libraries are implemented.
- [MODULES.md](MODULES.md) proposes a dependency-safe Lean/project structure.
- [REVIEW.md](REVIEW.md) is the adversarial review protocol and sign-off form.
- [DECISIONS.md](DECISIONS.md) records settled choices and rejected shortcuts.
- [REFERENCES.md](REFERENCES.md) is the initial source and design-lineage register.
- [GLOSSARY.md](GLOSSARY.md) fixes vocabulary used across the corpus.

## Normative language

“Must”, “must not”, “required”, and “prohibited” are normative. “Should” is a
strong default requiring written justification to violate. “May” is optional.

## Review completion

The corpus is approved only when reviewers can answer all questions in
[REVIEW.md](REVIEW.md), every cross-document link resolves, all terms have one
owner, and no open issue can change a foundational Lean interface.
Known target sketches must expose obvious blockers, but future unlike targets
may extend a versioned interface through reviewed migration/refinement theorems;
approval does not claim permanent sufficiency.
