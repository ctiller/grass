# Adversarial review protocol

Reviewers should attempt to break the design, not confirm its intent. Approval
means the interfaces can be implemented without silently choosing a foundational
semantic policy.

## 1. Review order

1. Read [FOUNDATION.md](FOUNDATION.md) and identify every trust escape.
2. Review [SEMANTICS.md](SEMANTICS.md) against finite, infinite, concurrent,
   interruptible, faulting, and hostile-environment executions.
3. Review [MEMORY_MODEL.md](MEMORY_MODEL.md) and [OBLIGATIONS.md](OBLIGATIONS.md)
   together; attempt alias, lifetime, race, teardown, and failure attacks.
4. Trace one high-level effect through [REFINEMENT.md](REFINEMENT.md),
   [INSTRUCTIONS.md](INSTRUCTIONS.md), and [PLATFORM_ABI.md](PLATFORM_ABI.md).
5. Attempt to prove one program while emitting a different artifact using gaps in
   [ARTIFACTS.md](ARTIFACTS.md) and [VERIFIED_PROGRAM.md](VERIFIED_PROGRAM.md).
6. Challenge every external assertion using [VALIDATION.md](VALIDATION.md).
7. Walk the Hello World acceptance chain end to end.

## 2. Mandatory attack questions

### Proof and semantics

- Can a friendly oracle, scheduler, or API response make the proof easier than
  the normative relation permits?
- Can an infinite internal spin satisfy a reactive-loop contract?
- Can fuel exhaustion be mislabeled success or failure?
- Can an observation projection hide a safety, ABI, or obligation violation?
- Are finite and infinite refinement claims distinguished?
- Does the final theorem range over executions loaded from the exact returned
  bytes, with inclusion oriented from bytes back to the proved program?
- Does the certificate prove that those bytes actually load for every admissible
  base/import environment, or is `Loads` an empty premise?
- Are the admissible base/import domains independently inhabited and defined
  without using `Loads` or execution existence? Is every loader result a valid
  initial state?
- Are initial execution and API response domains inhabited, including explicit
  pending behavior for calls that may block forever?
- Does every valid terminal initial state produce a zero-step conforming
  execution with result, observation, ABI state, and terminal obligations?
- Does an environment-contract violation terminate full assurance at the maximal
  safe prefix, rather than receiving normal specification conclusions?
- Does each executable weak-memory prefix extend one coherent graph witness, or
  can locally plausible choices compose into a globally forbidden execution?

### Memory and concurrency

- Can integer/address equality revive dead provenance or forge a pointer?
- Can partial byte copying accidentally preserve a pointer?
- Can one loan be returned twice, or teardown happen while another holder lives?
- Can arena reset make an old pointer valid at a reused address?
- Can a memory-affecting operation bypass the sealed event/access interface?
- Can two unordered ordinary writes to one byte be admitted?
- Does an atomic access incorrectly authorize non-atomic access?
- Are interrupts, faults, DMA, or external writes able to evade the event graph?

### Obligations and control flow

- Can a jump/call reach a block without satisfying registers, stack, memory,
  ghost, and obligation entry demands?
- Can a macro hide a fault, interrupt point, or obligation?
- Can success, failure, cancellation, process exit, or a callback lose an
  obligation?
- Does `abandonedUnknown` remain visible to the specification?
- Is terminal obligation correctness indexed by the exact result/observation
  contract rather than only by a permissive platform profile?

### Providers, ISA, and platform

- Can one nominal provider key resolve to incompatible implementations?
- Is the exact provider environment/dictionary used by upstream proofs retained
  through realization rather than rediscovered by typeclass search?
- Can code accidentally use both Vulkan and Metal as one global graphics API?
- Is every common x86 rule supported by anchored Intel and AMD citations?
- Is a feature used without CPUID/mode/profile applicability proof?
- Are API output buffers and partial results modeled dependently?

### Serialization and artifacts

- Can a parser overflow or allocate based on unchecked lengths?
- Does every writer value parse back exactly?
- Is canonicalization specified for every accepted alternate encoding?
- Can PE layout, relocation, import resolution, IAT patching, permissions,
  unwind data, or entry state diverge from the verified raw model?
- Can unknown/indirect code become reachable outside the typed CFG?
- Can an export table advertise a callable without its verified ABI contract?

### Trust and validation

- Is any behavior justified only by repository prose, folklore, one emulator, or
  one physical machine?
- Can a failed probe be discarded without becoming a ratchet item?
- Do fuzzing claims overstate finite coverage?
- Is an external library called in a way its model did not admit?
- Can an axiom, `native_decide`, generated source, assembler, or linker enter the
  trusted path without appearing in a ledger?
- Does the axiom audit inspect transitive dependency theorems and reject every
  constant outside the exact reviewed Lean-foundation allowlist?
- Does the published corpus leak personal paths, hostnames, serials, credentials,
  or irrelevant workstation topology?

### Standard library and proof economy

- Is `ByteArray` definitionally or theorem-connected to `Vec Byte`, or have two
  byte-container foundations appeared?
- Are logical `Vec` theorems independent of capacity, address, allocator, and
  target representation?
- Are pure `Vec` and physical `OwnedVec` distinct, with `Represents` preventing
  extensional equality from transporting provenance or release obligations?
- Are stable vector identity and generative buffer identity separate across
  reallocation, with the new buffer identity returned existentially?
- Does reallocation return a world-relative freshness witness and inequality,
  rather than treating an existential identity as automatically fresh?
- Are capacity, allocation failure, mutable slices, and loan identities absent
  from the pure `Vec` API?
- Can reserve/reallocation invalidate a live slice or pointer without consuming
  its unique loan?
- Do fallible bulk operations clean up partially constructed elements and
  allocator obligations?
- Does basic reallocation fail only before transfer and then use infallible
  relocation, or fully specify an exception-safety result for every element?
- Are consumers re-proving vector buffer invariants instead of using the shared
  logical/representation/allocator proof packages?
- Is the import graph acyclic—`Std.Logical` below memory/obligations and
  `Std.Owned` above them—with generic ownership facts having one lower owner?

## 3. Corpus consistency gates

Before implementation begins:

- all relative links resolve;
- normative terms have exactly one owner;
- every `VerifiedProgram` demand has a construction path and rejection behavior;
- every raw physical effect has a ghost-layer representation or explicit proof
  that none is required;
- known future targets expose no blocker without a versioned migration path;
- no unresolved initial-profile issue changes the kind or indices of a
  foundational type.

## 4. Sign-off

```text
Reviewer:
Date:
Revision/commit:

Foundation/trust:       approve | reject
Execution semantics:    approve | reject
Memory/concurrency:     approve | reject
Obligations:            approve | reject
Refinement/providers:   approve | reject
ISA/API/ABI:            approve | reject
Artifacts/connection:   approve | reject
Validation/citations:   approve | reject
Hello World readiness:  approve | reject

Blocking findings:
Nonblocking findings:
Required ratchet gates:
Residual trust accepted:
```
