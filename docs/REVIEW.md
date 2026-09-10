# Adversarial review protocol

For implementation work, start with [implementation peer review](#implementation-peer-review).
The design review order, attack questions and sign-off form below apply to the
relevant semantic boundary or major spike review, not every commit. Select the
questions that challenge the changed claim; do not replay the entire catalog for
routine proof bodies or packaging.

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

### Standard library and proof economy

Apply the accepted [shared-guarantee and second-consumer guidance](../CONTRIBUTING.md#shared-guarantees-and-second-consumers):
identify the guarantee's owner, assess actual adoption or the architecture-approved
exception, and ask what a third consumer would need to prove. The linked trial
inventory is bounded audit evidence, not a cleanup schedule.

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
files, kernel checks, and runtime probes under the structural, graph-simulation,
and calibrated-build ratchet in [OLEAN_SHARDING.md](OLEAN_SHARDING.md).

### 4.1 Authority of documented Lean

Normative prose may use Lean-shaped blocks for two different jobs, and review
must not confuse them:

- An **exact Lean interface** fixes the complete binders, indexes, field types,
  and result type which an implementation or another owner may consume. The
  introducing sentence labels it `Exact Lean interface` and cites the actual
  dependency-minimal Lean signature module. Nominal structures, classes,
  inductives, constructors, fields, projections, universes, and public
  attributes are declared once in that module; documentation does not restate
  them as an independently authoritative shadow declaration. A not-yet-defined
  function type or theorem proposition may be exported there as a closed
  signature alias. The later declaration is typed by that alias directly, or
  the signature or test module contains a checked inhabitation such as
  `example : Alias := declaration`; prose comparison of two restated types is
  not evidence of identity. A checked inhabitation lives in a signature module
  under the owning `Grass/**` tree or a test module under `Tests/**`; both trees
  are included by the ordinary Lake build. A Lean file outside those Lake-built
  module trees is not checked evidence merely because it has a `.lean` suffix.
  In particular, `Spikes/**` files are authored-source mirrors unless a separate
  gate actually elaborates them. The checking module pins its imports,
  namespace, open scopes, notation and relevant options, uses
  `set_option autoImplicit false`, and contains no holes, metavariables,
  ellipses, admissions, axioms, or unresolved names. Review records the checked
  declaration names, normalized types, attributes, and referenced-name set.
  Proof bodies may be described outside the block, but their propositions are
  complete. If the required vocabulary does not yet exist sufficiently to build
  that module, the block remains schematic. The signature module fixes types;
  it does not assert that a promised proof or implementation exists.
- **Schematic Lean** displays a construction, proof route, law family, or
  possible spelling without freezing binder order or proof plumbing. The
  introducing sentence labels it `Schematic Lean`. An ellipsis anywhere in a
  binder, field type, result type, or declaration header makes a block
  schematic whether or not it was labelled. Its normative content is the
  surrounding stated obligation and proof sketch, not an exact Lean API.

The language tag ``lean`` is syntax highlighting, not an authority class. A
block without ellipses is not automatically exact. New or materially edited
blocks must carry one of the two labels. A new or materially edited unlabelled
block is treated as schematic and the missing label is a review defect the
author must repair; it cannot be used as exact evidence while that defect is
open. Every pre-existing unlabelled documentation block is schematic by
default, regardless of how complete it looks; an already
implemented API obtains authority from its checked module, not its duplicate
prose rendering. No repository-wide relabelling is required. New cross-owner
reliance on a documented future boundary requires its owner to supply the exact
classification and signature module first.

An author may not nominate elaboratability, normalized type identity, or any
other exactness-dependent review target over a schematic block. The nomination
instead names the exact declaration or alias and its `Grass/**` signature
module. If that checked surface does not exist yet, the honest target is the
schematic design's semantic adequacy and constructive feasibility, not a claim
that Lean has accepted its spelling.

Design approval may accept a schematic block only under the complete checklist
in [PROOF_FEASIBILITY.md](PROOF_FEASIBILITY.md) and the unavailable-phase rules
in [SPIKE_AUTHORING.md](SPIKE_AUTHORING.md): it states the fully quantified
semantic theorem family and proof-relevant inputs, constructive route, reusable
automation boundary, finite falsifying fixture, non-weakening fallback, total
construction/rejection path, and named implementation ratchet. Schematic status
relaxes Lean binder spelling, not the meaning, quantification, or acceptance
criteria. Review may not report the block as elaborated or use shape inspection
to close an elaboratability target. Conversely, review must not force
replaceable helper binders into the precious interface merely to remove an
ellipsis.

Authority classification is not implementation approval and creates no
exception to [FOUNDATION.md](FOUNDATION.md), the trust audit, non-vacuity rules,
connection checks, mutation suite, or applicable implementation ratchet. Before
an implementor publishes a cross-owner consumer of a schematic boundary, the
boundary owner supplies a separately reviewed exact interface and signature
module. Implementation acceptance then includes an elaborating positive
consumer and a negative rejection or mutation fixture which fails for the named
reason where the applicable ratchet demands one; it also includes transitive
axiom/unsafe auditing and every relevant non-vacuity and end-to-end connection
gate. Review summaries state which authority class was checked and carry
forward only the evidence appropriate to that class.

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

## Implementation peer review

Review changed meaning and computational behavior, not the number of commits,
proof scripts or contributing agents. Independent semantic review covers new or
changed statements, definitions, premises, quantifiers, non-vacuity, model and
external applicability claims, trust boundaries, artifact provenance, exact
receipt/consumer connections, and algorithms that change behavior. A correct
proof of the wrong theorem, or a conclusion supplied as a premise, does not close
an implementation obligation.

The central question is **“What bad behavior does this theorem allow?”** Look for
a behavior satisfying the hypotheses while escaping the intended guarantee:
vacuity, omitted outcomes/waits/divergence, an assumed conclusion, the wrong CALL
or artifact identity, a blocked subset hidden by unrelated progress, or a gap
between the model and emitted bytes. A small counterexample or model fixture is
useful when practical; this is not a mandatory per-lemma refutation report.

One semantic boundary review covers a cohesive slice and its subsequent routine
proof completion. The author identifies the semantic delta and relevant checks;
the domain owner or peer examines the actual statements, assumptions and
implementation connection. Architecture resolves cross-boundary questions. Reopen
review when those boundaries change, including imported definitions, typeclass
instances, reducibility or consumer wiring that change meaning without changing
the displayed theorem type. These are responsibilities, not new registration or
approval steps; authorized direct integration continues.

### Proof bodies and computed producers

Once the intended proposition, assumptions and actual implementation connection
are established, Lean typechecking and the automated trust audit are the proof
review for an erased proof body. Routine proof refactors, plumbing and packaging
under that unchanged boundary need targeted checks, not repeated independent
Sol or other agent reviews. Plumbing is routine only while exact state indices,
source/artifact identity and consumer binding retain their established meaning.

Classify by meaning, not `by` syntax: a tactic block can construct a `Type`-valued
receipt, program or checked producer with computational behavior. Changes to such
output need appropriate deterministic validation and semantic review when the
behavior or connection changes. Kernel acceptance alone does not establish that
a model describes a native API, ISA or other external implementation.

### Checks and evidence

The [foundation trust policy](FOUNDATION.md) still rejects `sorry`/`admit`,
unapproved axioms, `native_decide`, unsafe proof authority and unverified compiled
replacements (`implemented_by`, `extern`, `csimp`) in the verified dependency
closure. Kernel-checked decision procedures remain valid for their stated claims.

Automate deterministic inventories, dependency/axiom and compiled-override
checks, source mirrors and accounting. Run the relevant typechecking, trust and
targeted tests for the changed slice; record their actual scope and results.
A scoped audit names its declarations or imported module cohort and is not a
whole-root trust result. An unrelated baseline failure does not force repeated
full-tree audits to accept a bounded result; preserve that limitation explicitly.
An interface fixture does not demonstrate actual production adoption: inspect
or deterministically check the real consumer and its exact binding.

Use the relevant attack questions above for changed semantic boundaries. Maintain
discriminating negative controls for tests and audit tools, but do not repeat a
mutation campaign or proof-method report for every routine lemma. Repeat checks
when changed code, failures or unresolved concerns justify them. Keep one concise
slice-level conclusion with its evidence and open obligations; no per-commit
checklist, duplicate prose review or new human confirmation gate is required.

### Examples

- Replacing the proof of `CallProtocol.return?_callerPending_false` with shared
  checked laws, under the same proposition and semantic dependencies, uses
  typechecking and trust checks. It does not need another tactic review.
- Replacing exact `BehaviorCorrespondence` with directed
  `ImplementationConformance`, or changing a delivery's receiver effect or scope,
  changes the guarantee and requires semantic review.
- A second consumer using an established helper with unchanged semantics uses
  targeted checks and evidence of actual adoption. Changing its exact CALL
  receipt, source/artifact binding or interface reopens boundary review; compiling
  only an interface test does not close the production connection.
