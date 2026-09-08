# Adversarial review protocol

Every spike review must apply the cross-view audit in
[SPIKE_AUTHORING.md](SPIKE_AUTHORING.md). Reviewing only the annotated document
or only the comment-free authored directory is incomplete.

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
8. For HTTP/2 or a protocol layered over it, regenerate and audit
   [HTTP2_CONSTRAINTS.md](HTTP2_CONSTRAINTS.md): every captured requirement key
   must have one connected witness over the same provider, raw program, and
   artifact, and the inventory must introduce no independent semantic demand.

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

### Documentation claims and mechanized gates

- Does each strong documentation claim identify evidence at the claim's actual
  scope, or admit that no mechanism enforces it?
- Does a cited theorem, invariant, type restriction, fixture, or external
  validation boundary establish the English claim rather than merely resolve by
  name?
- Does a point fixture, finite corpus, or syntactic scan get promoted into a
  universal guarantee?
- Does a docstring describe its own declaration and immediate invariants, or
  duplicate a remote inventory, count, or repository-wide characterization?
- Does a proposed repository-wide documentation gate satisfy the entry standard
  in section 4, including ownership, scope, negative evidence, and rollback?

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

### Documentation assurance and mechanized gates

Public documentation is part of the assurance surface, but prose is not a
proof. The authoritative strong-claim vocabulary is: `ensures`, `ensuring`,
`prevents`, `preventing`, `cannot`, `preserves`, `guarantees`, `makes it
impossible`, `is enforced`, `only if`, `only when`, `exactly`, and
`append-only`. A sentence using that vocabulary must identify the narrow evidence
that supports it: a checked theorem or transition invariant, a type restriction
that makes the contrary case unrepresentable, a named executable fixture, or an
explicitly external validation boundary. The claim states that evidence's actual
scope and does not promote a point fixture, finite test corpus, or syntactic check
into a universal guarantee. When no mechanism enforces the statement, the prose
says so.

Docstrings explain their own declaration and its immediate invariants. They do
not duplicate remote declarations, counts, inventories, or repository-wide
characterizations that silently become stale. Wider motivation, proof sketches,
and review history belong in the owning design or implementation document, where
their non-normative or not-yet-connected status can be stated honestly.

A static documentation audit is ordinary tooling, not semantic authority. It
may cheaply enforce an explicitly syntactic contract such as “a strong-claim
sentence carries a resolvable evidence reference”; it may not report that the
referenced evidence proves the English claim. The `docstring-audit` binary in
`tools/grass-tools` is ratified here as a repository-wide, deliberately
under-reporting check for a machine-recognizable subset of the vocabulary above.
It predates this checklist in its former Python implementation and remains
authoritative only for its documented syntactic contract and governed
`Grass/**/*.lean` paths; its green result is not proof that no comment
overclaims. Replacing its implementation does not silently change that contract;
the compatibility and review-record rules in
[AGENT_REVIEW.md](AGENT_REVIEW.md) still apply.

Before a new audit, or an expansion of an existing audit's defect class or
governed paths, becomes a repository-wide mandatory gate, its proposal requires
design review and tooling ownership. The review records:

- its implementation-independent accepted inputs, outputs, and failure modes;
- the exact defect class and governed paths;
- positive, false-positive, and false-negative fixtures;
- a mutation or equivalent negative test showing that the live gate is wired;
- bounded local and clean-run cost, portability, and deterministic diagnostics;
- rollout, exception ownership, versioning, and rollback; and
- why a narrower proof, type, owner-local check, or human review question is
  insufficient.

An implementation plan may require owner-local checks for its own candidate, but
does not by itself grant them authority over every other owner. A fleet-wide gate
obtains that authority from corpus-level design review such as this section, not
from the plan that first proposed its rule.

The six additional scanner classes proposed in `c-mem:61` are rejected as one
unreviewed fleet-wide bundle, while remaining eligible for separate proposals:

- **citation** reports a Lean-comment reference whose declaration name cannot be
  found;
- **projection-use** reports a structure-field name with no lexical projection
  site;
- **constructor-use** reports an inductive constructor with no lexical
  construction site outside its declaration;
- **fixture-use** reports a test definition with no lexical consumer;
- **file-reachability** reports a tracked Lean source reached by neither a build
  target nor an audit; and
- **authority-door** reports a lexical call to a designated state-mutating door
  from outside its per-door caller allowlist.

These are candidate defect classes, not findings about semantics. Each must
return through the gate-entry process above with determinate scope,
false-positive and false-negative evidence, ownership, cost, and rollback. This
records the question and proposal in `c-mem:61`, the initial ruling in
`g-design:172`, and the review corrections in `c-reviewer:153`.

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
files, kernel checks, and runtime probes under the structural, graph-simulation,
and calibrated-build ratchet in [OLEAN_SHARDING.md](OLEAN_SHARDING.md).

## 5. Sign-off

For a pre-implementation spike review, sign-off distinguishes `design approve`
from `implementation approve`. The former applies the design-fixpoint rules in
[SPIKE_AUTHORING.md](SPIKE_AUTHORING.md) and must not demand that the prohibited
library already exist. The latter requires real generated evidence, mutation
runs, artifact bytes, kernel checks, and scale measurements under
[IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md). A reviewer may
reject a missing or unbelievable proof sketch at design time; it may not call
honestly unavailable execution evidence a design defect while the library is
explicitly out of scope.

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
