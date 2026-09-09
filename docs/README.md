# Grass specification corpus

Status: target design with a partial foundation implementation. The five spike
sources remain acceptance fixtures until they compile and close the required proofs.

This corpus defines the interfaces and proof demands that implementation must
meet. A later implementation may reveal that an interface is inconvenient; it
may not silently weaken a demand. Changes to a normative demand require an
explicit decision record and renewed review of affected documents.

## Find code and current evidence

- [Endpoint index](ENDPOINT_INDEX.md): start at authored `helloVerified` and
  `bytes`, then find implemented components, remaining connections and authors.
- [Validation command map](CHECKS.md): choose a check by the claim it supports,
  including fresh source and ledger audits.
- [Module structure](MODULES.md): intended dependency direction; proposed paths
  are not an inventory of implemented modules.

These navigation pages do not replace the normative owners below.

## Authority

When documents conflict, authority is:

1. [FOUNDATION.md](FOUNDATION.md) for scope, trust, and non-negotiable laws.
2. The narrowly owning normative document listed below.
3. [DECISIONS.md](DECISIONS.md) for ratified interpretations not yet folded in.
4. Examples and implementation notes.

No document may override a narrower owner by restating it differently.

## Normative owners

| Document | Owns |
|---|---|
| [VISION.md](VISION.md) | large-system target, proof-economy priorities, spike interpretation |
| [FOUNDATION.md](FOUNDATION.md) | mission, trust boundary, repository laws |
| [SEMANTICS.md](SEMANTICS.md) | executions, nondeterminism, observations, safety, progress, liveness |
| [RESOURCES.md](RESOURCES.md) | semantic resource budgets, physical execution envelopes, and their realization theorem |
| [SPECIFICATION_LANGUAGES.md](SPECIFICATION_LANGUAGES.md) | open family of precious DSL fragments and their typed semantic junctions |
| [GRAMMAR.md](GRAMMAR.md) | precious text/binary languages, incomplete versus invalid prefixes, parser/writer realization laws |
| [PROCESS.md](PROCESS.md) | portable state/event/demand/view processes, networks, channels, flattening, resources, and driver boundary |
| [PROCESS_SHARDING.md](PROCESS_SHARDING.md) | open process registries, facet certificates, scoped cancellation, SCC summaries, and rebuild cones |
| [VERIFIED_PROGRAM.md](VERIFIED_PROGRAM.md) | the public certificate and emission gate |
| [VERIFIED_OBJECTS.md](VERIFIED_OBJECTS.md) | stable subsystem signatures, relocatable verified objects, modular linking |
| [OLEAN_SHARDING.md](OLEAN_SHARDING.md) | Lean module boundaries, `.olean` reuse, certificate DAGs, and rebuild cones |
| [IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md) | future spike commands, evidence schemas, mutations, and implementation sign-off |
| [MEMORY_MODEL.md](MEMORY_MODEL.md) | memory, provenance, borrowing, concurrency, faults |
| [OBLIGATIONS.md](OBLIGATIONS.md) | linear obligations, transfer, exit dispositions |
| [REFINEMENT.md](REFINEMENT.md) | refinement proof concerns, weaving, provider realization, generated/authored machine routes |
| [ASSEMBLY_CONSTRUCTION.md](ASSEMBLY_CONSTRUCTION.md) | typed layouts, physical placement, verified generated instruction fragments, literal escape |
| [INSTRUCTIONS.md](INSTRUCTIONS.md) | extensible operations, ghost erasure, raw instructions, ISA profiles |
| [PLATFORM_ABI.md](PLATFORM_ABI.md) | platform plans, APIs, ABIs, Win32 x64 baseline |
| [ARTIFACTS.md](ARTIFACTS.md) | parsers, writers, PE/COFF, relocation, connection theorems |
| [VALIDATION.md](VALIDATION.md) | citations, probes, fuzzers, TCB ledgers, CI gates |
| [STDLIB.md](STDLIB.md) | fundamental data structures and reusable proof laws |
| [PROTOCOL_STDLIB.md](PROTOCOL_STDLIB.md) | candidate protocol-package shape, staged obligations, and HTTP/2/gRPC composition |

Development follows the spike-first rebuild workflow in
[CONTRIBUTING.md](../CONTRIBUTING.md). Former coordination documents and
implementation plans are retired; references to their sections in older code
comments are historical provenance available in Git, not active instructions.

## Review and delivery

- [DISASM.md](DISASM.md) proposes the imported-binary evidence pipeline and
  memory-safety proof boundary; [DISASM_CORPUS.md](DISASM_CORPUS.md) proposes
  acceptance using spike outputs followed by safe and unsafe compiled C fixtures.
  These are feature proposals, not new normative owners or implementation claims.
- [VISION.md](VISION.md) explains the large-system objective and the tradeoffs
  against which spike proof economy is judged.
- [PROOF_FEASIBILITY.md](PROOF_FEASIBILITY.md) gives constructive proof sketches,
  automation limits, falsification fixtures, and fallbacks for mechanisms
  challenged as implausible.
- [SPIKE_AUTHORING.md](SPIKE_AUTHORING.md) defines the two spike views, authored
  versus generated accounting, and the mandatory cross-view review.
- [SPIKE_PROOF_BURDEN.md](SPIKE_PROOF_BURDEN.md) assigns every spike-shaped
  theorem and invariant family to authored, library, generated, or authority
  work instead of treating a short identifier as evidence of a short proof.
- [HELLO_WORLD.md](HELLO_WORLD.md) defines the first acceptance milestone.
- [HELLO_UNWIND_BOUNDARY.md](HELLO_UNWIND_BOUNDARY.md) records the reviewed
  Hello unwind/PE binding interpretation of the existing ABI, artifact and
  milestone requirements; those normative owners retain authority.
- [SPIKE1_BOUNDARY_REVIEW.md](SPIKE1_BOUNDARY_REVIEW.md) records the console
  interface review, ownership and remaining proof obligations; it is a review
  snapshot, not a replacement normative contract.
- [HELLO_FACADE_BOUNDARY.md](HELLO_FACADE_BOUNDARY.md) records the required
  unchanged-source facade/root signatures, owners and reviewed terminal
  observation direction; it does not claim the migration is implemented.
- [SPIKE_1.md](SPIKE_1.md) is its annotated proof from portable specification to
  emitted Win32 PE bytes.
- [SORT.md](SORT.md) defines the second acceptance milestone.
- [SPIKE_2.md](SPIKE_2.md) is the annotated proof proposal for an in-memory stable,
  allocation-aware stdin byte-line sort.
- [GZIP.md](GZIP.md) and [SPIKE_3.md](SPIKE_3.md) define and fully lower the
  bounded-memory streaming gzip milestone.
- [WEB_SERVER.md](WEB_SERVER.md) and [SPIKE_4.md](SPIKE_4.md) define and fully
  lower the cancellable multiplexed in-memory cleartext HTTP/2 server milestone.
- [HTTP2_CONSTRAINTS.md](HTTP2_CONSTRAINTS.md) is the mechanically keyed audit
  projection from the precious HTTP/2 spec to implementation witnesses and the
  extension seam for a later gRPC suite.
- [PROTOCOL_STDLIB.md](PROTOCOL_STDLIB.md) proposes the reusable package imported
  by protocol spikes so applications select profiles rather than hand-plumbing
  grammars, parsers, error matrices, and process demands.
- [CUBE.md](CUBE.md) and [SPIKE_5.md](SPIKE_5.md) define and fully lower the
  Win32/Vulkan/SPIR-V spinning-cube composition milestone.
- [../Spikes/README.md](../Spikes/README.md) indexes the matching comment-free
  expected Lean source files, including final PE emission and connection
  theorems. They are design fixtures until the Grass libraries are implemented.
- [MODULES.md](MODULES.md) proposes a dependency-safe Lean/project structure.
- [OLEAN_SHARDING.md](OLEAN_SHARDING.md) specifies how bounded source shards,
  public signatures, opaque certificates, Lake facets, and aggregate `.olean`
  modules localize proof and build invalidation.
- [IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md) fixes the future
  command, report, mutation, and first-failure contract without claiming that
  the deliberately deferred library or outputs exist.
- [REVIEW.md](REVIEW.md) is the adversarial review protocol and sign-off form.
- [DECISIONS.md](DECISIONS.md) records settled choices and rejected shortcuts.
- [REFERENCES.md](REFERENCES.md) is the initial source and design-lineage register.
- [GLOSSARY.md](GLOSSARY.md) fixes vocabulary used across the corpus.

## Implementation notes and historical assessments

These complement the owner documents and review records above. Read each
note's revision and limitations before relying on its implementation status.

| Topic | Entry points |
|---|---|
| Windows format, loading and API behavior | [PE model](WINDOWS_PE.md), [loader initialization](WINDOWS_LOADER_INITIALIZATION.md), [WriteFile](WINDOWS_WRITEFILE.md) |
| Bounded instruction and memory execution | [x86 execution](X86_EXECUTION.md), [Hello instruction coverage](X86_HELLO_COVERAGE.md), [source-derived frame memory](FRAME_MEMORY_EXECUTION.md) |
| External instruction source migration | [AMD APM source migration](AMD_SOURCE_MIGRATION.md) |
| Historical vocabulary and recorded defects | [memory vocabulary assessment](MEMORY_VOCABULARY.md), [resource-class elaboration defect](DEFECT_SEMANTICS_RESOURCE_CLASSES.md) |

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
