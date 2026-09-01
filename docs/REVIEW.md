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

- Is the precious specification a function of an explicit selected resource
  model, with only the bounded law-bearing capability classes it needs? Does a
  platform-independent model/process theorem prove the selected instance before
  assembly refinement begins?
- Does the target projection prove preservation rather than moving demanded
  product behavior into a replaceable target mapping?
- Can a second assembly realization reuse the same portable correctness theorem
  without re-proving product logic?
- Can a friendly oracle, scheduler, or API response make the proof easier than
  the normative relation permits?
- Can an infinite internal spin satisfy a reactive-loop contract?
- Can fuel exhaustion be mislabeled success or failure?
- Can an observation projection hide a safety, ABI, or obligation violation?
- Are finite and infinite refinement claims distinguished?
- Does the final theorem range over executions loaded from the exact returned
  bytes, with inclusion oriented from bytes back to the proved program?
- Does the certificate prove that those bytes actually load for every admissible
  execution-context/base/import triple, or is `Loads` an empty premise?
- Are the admissible context, base, and import domains separately and
  independently inhabited and defined without using `Loads` or execution
  existence? Is every loader result a valid initial state for the exact context?
- Are initial execution and API response domains inhabited, including explicit
  pending behavior for calls that may block forever?
- Does every valid terminal initial state produce a zero-step conforming
  execution with result, observation, ABI state, and terminal obligations?
- Does an environment-contract violation terminate full assurance at the maximal
  safe prefix, rather than receiving normal specification conclusions?
- Does an infinite pending trace carry only trace refinement and progress rather
  than a fabricated completed result or accepted terminal observation?
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
- Can a provider strengthen a portable liveness premise, or is there a named
  implication to its fixed abstract meaning and a coherent inhabitance witness?
- Does responsiveness quantify over every maximal continuation generated by a
  branching strategy, rather than exhibit one favorable terminating history?
- Does every terminal-status provider prove preservation, reflection,
  distinguishability on the demanded values, and pending/resource fidelity?
- Is terminal reflection restricted by independently defined reachability from
  this program's demanded statuses rather than the provider's entire domain?
- Is post-environment-violation containment an explicit implementation choice
  rather than an invisible assembly verification requirement?
- Does each containment tail consume an exact result-indexed violation envelope,
  with arbitrary memory/ABI/control violations receiving no typed continuation?

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

- Does the precious resource-parameterized specification state only demanded
  product observations and guarantees, while a replaceable portable process model
  relates those observations to their generating transitions without fixing its
  population, routing, supervision, or state partition in the precious source?
- Does the reviewed `ProcessPlan` say exactly which process instances may exist,
  what local/shared logical state they access, and which channels connect them?
- Does every channel have exclusive Hoare-style send/receive classification for
  message occurrences, state/ownership transfer, obligations, and framing, with
  a stable in-flight escrow preserved under unrelated process steps, an affine
  at-most-one receive/disposition token, and conditional—not assumed—eventual
  resolution?
- Can a serial authoring input synthesize and then flatten its degenerate plan
  back to the original relation, while an explicit subsystem can flatten into a
  reusable parent process without exposing its weave?
- Are syscall reorderings justified by graph-level independence diamonds rather
  than post-hoc equality of flattened traces?
- Is every external/API/library call with entropy, pending, intermediate
  effects, independent cancellation, or observable interleaving a child process
  protocol covering dependent results, fault, violation, and terminal states?
  Conversely, does a terminating frontier-free serial function remain a local
  Hoare/CFG call with exhaustive exits and a finite-stuttering simulation?
- Is each large global loop proved through an inspectable
  `ProcessLoopInvariant`, with every raw dispatch path implementing one named
  process transition and re-establishing the network relation?
- Can a materially different `ProcessPlan` realize the same precious spec
  without compatibility coercions or retained generated identities?

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
- Is every physical struct layout an explicit reviewed construction choice, with
  derived offsets and bounds but author-owned assembly indexing and stores?
- Has a compact representation hidden an artificial 32-bit size limit or lost
  the ghost occurrence identity required by the specification?
- For a change to bytes, outcome policy, liveness, provider plan, or one assembly
  block, is the invalidation cone explicit and limited to semantic dependents?
- Do generated proof, symbol, CFG, loan, or layout identities leak upward and
  force unrelated precious specifications or local certificates to change?
- Can the build explain proof invalidation, or does a monolithic certificate
  cause whole-program re-proving after a local edit?
- Is the import graph acyclic—`Std.Logical` below memory/obligations and
  `Std.Owned` above them—with generic ownership facts having one lower owner?
- Do partial read/write boundaries leak into parser, codec, or application
  meaning, or are all legal rechunkings proved equivalent over one byte flow?
- Does a partial write transfer exactly one positive prefix and leave a unique
  retry suffix, including pending, failure, cancellation, and close races?
- Can the resource certificate project a bound for any named process subtree,
  including its dynamic descendants, channel escrow, stacks, and layout
  overhead, without double-counting affine loans or shared read-only regions?
- Does a finite memory claim make an over-capacity send impossible through
  affine capacity credit and an explicit backpressure frontier, or merely assume
  producers will not outrun consumers?
- When composing resource bounds, is the use of sum, maximum, shared-once, or
  transfer justified by interference/lifecycle facts rather than chosen to make
  the number fit?
- Does a serial routine remain an ordinary local Hoare CFG with no authored
  process annotations, while still normalizing to the common process semantics
  for composition? Measure adapter elaboration/cache cost rather than proposing
  a second semantics merely to avoid generated proof structure.
- Can the same serial subsystem later be pipelined, threaded, supervised, or
  embedded under a callback/GPU process without rewriting its failure,
  liveness, obligation, observation, and resource contracts?
- Is the exact authored machine source the value elaborated, ghost-erased,
  encoded, linked, loaded, and decoded, or could an extensionally equivalent but
  different raw program satisfy disconnected fields?
- Does the selected process-model run maintain linear outstanding demand multiplicity,
  with concrete occurrences erasing bijectively and every terminal state
  classifying remainders?
- Are child occurrences indexed by exact parent-local demands, with only a
  proved partial projection to exported driver demands?
- Does nominal freshness include tombstoned history across completion, restart,
  coalescing, and numeric reuse, with affine authority in owned escrow rather
  than a duplicable structure field?
- Does serialization preserve and reflect every execution/result/lifecycle
  branch, keeping fairness separate and demanding linearizability for overlap?
- Does replay bind the exact theorem type and transitive semantic/toolchain/audit
  environment, using Merkle roots only to locate candidates? Are source hashing,
  equality construction, kernel replay, composition, and artifact regeneration
  measured separately rather than calling all of them one “scan”?

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

## 4. Product and SDLC gate

A proof-friendly program is not accepted merely because its theorem is small.
For every spike, reviewers classify each simplification as:

- a precious semantic/product choice that must remain visible in the spec;
- a replaceable implementation choice that is still reasonable to ship; or
- a proof-only allowance that damages behavior, performance, robustness, or
  operability and must be removed.

Review the real artifact: input sizes, failure behavior, diagnostics, resource
use, asymptotic complexity, platform conventions, security defaults, and tuning
freedom. Ask whether a competent systems programmer would ship it for the stated
scope. “It made the proof easier” never justifies an otherwise unacceptable cap,
silent data loss, unstable result, quadratic hot path, disabled hardening, or
unmodeled platform assumption.

An end-to-end spike must reach its actual machine languages. Every algorithmic,
flow-control, concurrency, API, cleanup, and error path appears as authored raw
instructions (plus explicit ghost annotations) or as the transparent expansion
of a displayed proved macro. A named contract may establish a reusable local
proof boundary, but it may not stand in for an omitted helper body. Static data,
imports, cross-ISA modules, relocations, terminal paths, and exact artifact
emission are part of the same review. Pseudocode with an unexpanded “do the
algorithm” comment is not an end-to-end spike.

Then change each precious spec field independently and inspect the invalidation
cone. Local semantic changes should reopen local contracts; generated identity
churn and monolithic re-verification are architecture failures.

Also review author ceremony independently of the audit fixture layout. Count
the declarations and proof terms an application author must maintain, not the
generated certificate projections shown for adversarial inspection. A public
closing form should permit cohesive co-location for a small program and measured
sharding for a large one. Reject required copy-pasted writer round trips, manual
source slicing, ABI boilerplate, or containment tails when an exact transparent
constructor can generate them; retain the ability to replace every constructor
with literal assembly and an explicit adjacent proof.

Performance review must include at least one tuned alternative for important hot
families—SIMD scanning, polynomial checksums, atomics, flow control, graphics,
or equivalent—and a local extensional-equivalence proof route. A scalar
reference implementation is not evidence that optimized assembly is
economical. Conversely, estimated speedups and invented module counts are not
evidence: record instruction mix, proof/elaboration work, cache reuse, generated
files, kernel checks, and runtime probes on the stated scale fixtures.

## 5. Sign-off

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
In-memory sort readiness: approve | reject
Streaming gzip readiness: approve | reject
HTTP/2 server readiness:  approve | reject
Vulkan cube readiness:    approve | reject
Authoring ceremony:       approve | reject
Large-system scale gates: approve | reject

Blocking findings:
Nonblocking findings:
Required ratchet gates:
Residual trust accepted:
```
