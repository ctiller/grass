# Milestone 2: in-memory stable stdin byte-line sort

The complete annotated proof proposal is [SPIKE_2.md](SPIKE_2.md). This file is
the concise acceptance checklist.

## Specification

- Input is an arbitrary finite LF-delimited byte stream; CR, NUL, and non-UTF-8
  bytes are ordinary record content.
- A nonempty EOF suffix is a final record; output appends LF to every record.
- Records are ordered lexicographically by unsigned byte value.
- Equal records preserve their input occurrence order through a machine-level
  descriptor-identity theorem, even though stdout bytes cannot distinguish them.
- Success writes exactly the normalized stable-sorted stream and status zero.
- Every failure returns the specified nonzero status. Allocation or checked-size
  exhaustion and every pre-output input failure write no stdout bytes. Output
  failure may leave only a proved prefix of the required stream.
- No fixed application size/count/line limit is permitted below checked machine
  representability; allocator failure remains explicit entropy.
- Termination is conditional on eventual EOF and universal responsive-strategy
  assumptions. Safety and finite work between frontiers are unconditional.

The format, order, outcomes, resource policy, and progress law above are the
only precious semantic source. They do not prescribe process count, process
state partition, channels, sorting algorithm, buffer size, allocator, API, ISA,
or artifact format.

## Process realization

- The unique standard sequential realizer is selected from the specification;
  it is inspectable but not application-maintained. `SequentialAdapter`
  synthesizes one root plus occurrence-indexed read,
  allocation, write, and terminal children in the universal process algebra.
- Collecting, metadata allocation, sorting, emission, and termination remain
  root logical phases. Pure stable sort is an extensional local transition, not
  a fictional concurrent actor. Input/allocation failures occur before the
  stdout-authority transfer.
- The generated plan has no shared logical region. Its typed Hoare channels
  escrow exact buffer loans, child results, and obligations; pending, failure,
  cancellation, death, and violation branches remain complete.
- The adapter supplies non-vacuous initial networks, child-choice completeness,
  coupled finite/infinite execution refinement, and global progress. The graph
  and proof are inspectable but not application-maintained.
- An explicit parallel, streaming, or external-storage plan may replace the
  generated plan by proving the same `spec` and stable `DriverBoundary`.

## Realization

- Win32 x64, Windows 10 API baseline, common Intel/AMD x86-64, PE32+ with ASLR.
- Exact providers: synchronous standard handles, `ReadFile`, `WriteFile`, process
  heap allocation/reallocation, and `ExitProcess`.
- Complete input `OwnedVec Byte`, compact 16-byte `(offset,length)` descriptors,
  and equally sized scratch descriptors are allocated before stdout authority
  exists. Source ordinal is a proof identity derived from scan position.
- Bottom-up stable mergesort selects the left descriptor on equal comparison.
- Output is staged through a 64 KiB, 64-byte-aligned writable static PE object.
  Arbitrarily long lines cycle through copy and flush; each flush handles all
  positive partial writes, failure, zero progress, pending, and excess-count
  violation, and success requires a final empty buffer. The fixed object costs
  64 KiB of loaded writable memory without adding an allocation-failure phase.
- The assembly author names fields in a declarative `SortFrame`; derived exact
  offsets, call alignment, non-overlap, unwind data, and literal lowered
  instructions remain inspectable. Literal displacement overrides remain legal.
- The spike displays the complete `sortSource : AsmSource plan` and exact lowering,
  including checked growth,
  both scans, stable merge loops, comparator, buffered copy/flush loops, failures,
  and static data. Its only macros have displayed raw expansions. Vector, slice,
  merge, ABI, unwind, erasure, encoding, layout, loader, and exact-byte proofs
  are reusable/generated without replacing those author-controlled instructions.
- `verify_assembly plan with sortSource`
  proves both boundaries: synthesized process plan to precious specification, then exact authored
  source/driver to process plan. The emitted program remains indexed only by
  `spec`, so neither process weave nor platform realization becomes precious.

## Acceptance chain

1. Portable parser/order/outcome/resource/liveness laws are well formed and
   universal over all input and environmental choices.
2. `SequentialAdapter` selects reusable child `ProcessCorrect` certificates and
   proves exact routing, demand-occurrence correlation, ownership transfer,
   observation filtering, non-vacuity, result completeness, and progress.
3. The Win32 plan proves dependent read/write/heap/terminal contracts, concrete
   branching-strategy coupling, and nonempty admissible domains.
4. The process allocation barrier and its source refinement prove no stdout
   event precedes all allocation and
   sorting success.
5. Every `OwnedVec` growth, failed reallocation, descriptor range, initialization
   phase, loan, provenance identity, and terminal disposition typechecks.
6. Writable-static provenance, buffer initialization/spare partition, pending
   flush loans, committed-prefix accounting, long-line chunking, and final flush
   typecheck without weakening output-failure observations.
7. The authored source proves stable permutation, sortedness, progress, ABI, memory,
   fault, interruption, and obligation contracts locally.
8. Erasure and semantic instruction encoding connect the exact raw program.
9. PE writer/reader/parser, imports, unwind, writable zero-fill `.data`, loader,
   and exact emitted-byte laws compose into `sortVerified.sound`.
10. A transitive axiom audit rejects `sorry`, unsafe proof authority,
   dependency-defined axioms, and `native_decide`.
11. Fuzzers/probes challenge vector growth, stable sorting, buffered partial
    writes, long lines, final flush, API boundaries, instruction models, PE
    parsing/loading, and Intel/AMD correspondence without replacing proof.

The milestone is not accepted merely because a native execution sorts example
files. The exact emitted bytes must carry the complete certificate above.

This milestone is shippable only for the stated in-memory, bytewise,
LF-normalizing, synchronous-standard-handle profile. It is not yet a universal
drop-in Windows `sort`: external spilling, locale collation, stderr diagnostics,
and adaptive support for inherited overlapped handles are explicit product
extensions rather than proof conveniences hidden in the baseline.
