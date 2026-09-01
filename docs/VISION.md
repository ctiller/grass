# Vision and scale target

## 1. What Grass is for

Grass exists to build large, long-lived, high-assurance software systems whose
implementation can be authored and tuned at machine level: game engines,
databases, operating-system kernels and services, compilers, storage engines,
graphics stacks, network services, and similarly demanding software. A system
may contain millions of lines of authored/generated assembly across multiple
ISAs and platform APIs. Hello World is the first microscope slide, not the
objective function.

The project optimizes for four durable assets:

1. a minimal precious Lean specification stating only the behavior and
   guarantees the product actually demands;
2. reusable implementation models which bank difficult algorithmic proofs;
3. first-class authored assembly whose exact instructions, layouts, ABIs, and
   optimization choices survive into the emitted artifact; and
4. small, stable contracts which let teams rebuild everything else locally and
   cheaply when specifications or implementations change.

Grass accepts some additional generated certificate structure—and, where the
semantics genuinely require it, some explicit author ceremony—in a trivial
program if that buys one compositional architecture which scales to the systems
above. It does not accept duplicated sequential/concurrent semantics, a second
memory or obligation theory, or a special “toy program” proof gate merely to
make Hello's internal proof object look smaller.

This trade is not permission for gratuitous boilerplate. Small programs are
valuable proof-economy tests. Standard cases should still let an author state a
specification, select a platform plan, write assembly, and close with
`verify_assembly plan with source`. The distinction is that generated internal
structure may be richer than this surface.

“One way” means one public correctness theorem and one family of compositional
contracts, not one physical execution strategy or one mandated authoring style.
A hand-scheduled SIMD loop, a direct function call, a serialized parser graph,
a worker pool, a callback-driven window, and an interrupt handler may have very
different machine realizations. They nevertheless close through the same
process, observation, safety, progress, obligation, resource, exact-source, and
artifact laws. Grass does not make users choose a weaker theorem architecture
when code grows beyond the shape of the first prototype.

## 2. One architecture, fractally applied

Grass uses one process semantics for composition, nondeterminism, lifecycle,
observations, progress, obligations, and resource accounting. The same algebra
describes a one-root sequential program, a lexer/parser/compiler pipeline, a
thread pool, an interrupt-driven kernel subsystem, and a host/GPU application.

That does **not** mean every function executes as an actor or that an assembly
author annotates ordinary instructions with channel proofs:

- straight-line regions and ordinary functions are verified locally with typed
  Hoare/CFG contracts;
- a process step may call such a terminating serial function directly, without
  manufacturing a child, channel, or runtime scheduling point;
- a standard sequential specification selects a proved canonical realization,
  so application code does not maintain synthetic process topology;
- an algorithm may be proved internally as a graph of cooperating passes, then
  flattened and serialized to one ordinary loop or function;
- genuinely concurrent implementations retain the graph and realize channels
  through queues, atomics, callbacks, interrupts, APIs, or devices; and
- any proved subsystem can be flattened behind one protocol and composed as a
  child of a larger graph.

The reason for retaining one semantic substrate is large-system change. A
sequential parser may later be pipelined, a renderer may move work to a GPU, a
database task may become cancellable, or a kernel service may acquire interrupt
entry. With one algebra, its failure, liveness, observation, obligation, and
resource contracts remain composable. With separate direct and process
semantics, each such evolution needs an adapter theory or a rewrite.

The process lens also owns causal attribution. Every projected byte, frame,
syscall, resource transfer, and terminal outcome is related to the exact logical
transition which generated it. Global ordering claims—such as “all stdout bytes
appear once and in program order”—then follow from local transition invariants,
channel escrow laws, and composition, rather than a fresh induction over the
flattened machine trace. Lower simulations preserve this attribution even when
the physical realization is serial, asynchronous, threaded, interrupted, or
split across host and device ISAs.

Refinement is fractal and may be heterogeneous across one graph. A graphics
subprocess can be lowered to Vulkan and SPIR-V while storage remains an abstract
disk protocol; storage can later be lowered to asynchronous Win32 I/O and IOCP
without reopening the graphics proof. Local replacement preserves a typed
protocol/resource/obligation/progress boundary and frames the rest of the graph.
Provider and platform requirements accumulate explicitly and are checked for
global coherence before verified emission.

The precious root `SpecProcess` does not store that lens. It captures a composition of
domain-appropriate specification-language fragments, their meaning-bearing
junctions, the one derived external behavior contract, and selected resource
semantics. `VerifiedProgram` is indexed by that exact root. A replaceable process
presentation can name connection sessions, typed request/response channels, and
linear per-session custody, then prove that its trace denotation is exactly that
contract. A fixed worker plan, proactor, coroutine loop, serialized executor, or
different abstract role decomposition can each supply such a presentation and
refinement without changing the precious value.

There is no mandated universal specification syntax. Relations, grammars,
protocols, reactive traces, temporal demands, resource policies, scenes,
schemas, and future domain languages share a typed `ContractFragment` interface.
Their junctions state semantic flow—such as bytes decoding to frames which drive
a protocol and route relation—not execution assignment. Every composed suite
still produces the single contract consumed by `VerifiedProgram`.

Grass distinguishes semantic blast radius from elaboration blast radius. The
process realization is a replaceable witness exported through a small
specification-satisfaction and boundary theorem; its private state and topology
do not enter the precious resource-parameterized specification function or
unrelated consumers.
Likewise, a basic block sees only its local Hoare contract, not the enclosing
network's demand multiset. Process composition is valuable only if these module
boundaries prevent a private state-field or register edit from reopening the
whole process proof graph.

The tempting alternative is a co-equal “direct sequential” semantics. Grass
rejects it because it saves generated structure at the smallest scale by
duplicating composition at the largest: byte I/O, cancellation, child work,
resource flux, fault propagation, and progress would need bridge theorems every
time a formerly local subsystem became asynchronous or concurrent. Local Hoare
contracts already provide the economical sequential authoring boundary. The
canonical sequential realization transports those proved contracts into the
one process theorem; it is a finite normalization of declared effects and an
existing correctness witness, never synthesis of arbitrary program structure.

## 3. Scale boundaries

Whole-system assurance is composed; it is not re-proved monolithically. The
normal scale boundaries are:

- instruction and straight-line block;
- loop or small sub-CFG;
- function and ABI profile;
- module/library with exports and hidden implementation;
- process/subsystem protocol;
- platform/ISA/artifact component; and
- final `VerifiedProgram` connection theorem.

Callers consume function/export contracts and do not reopen callees. Process
drivers consume process/channel contracts and frame untouched instances.
Algorithm assembly refines a selected Lean implementation model without
re-proving its mathematics. Artifact composition consumes exact component
identities and source-to-byte connections. A register allocation edit should
invalidate its local code certificate and dependent layout/call summaries, not
the specification or unrelated sibling modules.

These boundaries are also organizational boundaries. A large repository may
assign separate ownership to specifications, implementation models, platform
providers, assembly modules, and artifact profiles. Published exports hide
interiors behind versioned contracts; dependency manifests identify which
semantic facets a consumer actually used. Whole-program closure composes those
exports. It does not inline millions of lines into one proof term or require a
global symbolic execution pass.

The build architecture uses ordinary Lean modules and kernel checking. Grass may
generate measured proof shards and hierarchical content-addressed manifests,
but it does not replace or bypass the Lean kernel, import environment, or `.olean`
soundness model. Cache keys bind exact theorem types and transitive semantic,
profile, toolchain, verifier, option, and axiom-audit roots. Shard size is an
empirical build choice: one declaration per module is not a mandate, and a
custom sub-declaration kernel cache is not assumed.

## 4. First-class specification, models, and assembly

These artifacts have different jobs:

```text
resource-parameterized specification precious program meaning
        ↓
portable behavior proof             proves the behavior once
        ↓
process/protocol composition        reviewed, replaceable
        ↓
selected resource profile/proof     reviewed, configurable
        ↓
implementation model(s)             reusable proof bank, replaceable
        ↓
platform and ABI realization        reviewed, replaceable
        ↓
authored/generated assembly         first-class, tunable, replaceable
        ↓
exact raw instructions and artifact derived and connected
```

The portable boundary is tripartite in ownership and dependency:

```text
reviewed resource model
      ↓ parameter
precious specification family
      ↓
faithful target projection --> configured target boundary
```

The explicit resource-model value selects quantitative and lifecycle semantics
over an extensible resource algebra rather than memory alone. Law-bearing
typeclasses expose only the axes required by a specification; spec-specific
classes may stratify and extend them without one universal resource record. The precious specification
is a function of that model: `webServerSpec resources`, not a fixed behavior to
which resources are attached afterward. Thus the same web-server definition can
be instantiated for microcontroller limits or data-center capacity, while its
exhaustion, admission, backpressure, and failure behavior remains explicit. The
target projection
maps abstract lines, outcomes, clocks, capabilities, and calls into a coherent
platform/API/ISA profile and proves that mapping faithful. The specification
function is precious; the resource argument and
projection is replaceable unless a target-visible representation is itself
promised. Separating them gives resource-profile changes and ports narrow
invalidation cones without pretending that an allocation-failure policy
or connection bound is an unchecked implementation detail.

The first arrow is not decorative. Grass deliberately proves correctness at
the portable specification level and then proves that a selected assembly
realization refines that already-proved account. In schematic form:

```lean
specificationCorrect : PortableModelSatisfies productSpec portableModel
assemblyRefines      : AssemblyRefinesModel source representation portableModel
artifactIsAssembly   : LoadedArtifactRefinesSource bytes source

exactArtifactCorrect : LoadedArtifactSatisfies bytes productSpec
```

The theorem statement and the domain vocabulary it mentions are precious. The
portable model and proof may be rebuilt when the statement changes, but the
proof is established independently of any ISA, ABI, linker, or chosen assembly
implementation. This separation is the main proof-economy mechanism: a second
assembly implementation reuses `specificationCorrect` and proves only its own
adjacent refinement; an optimization which preserves the model does not reopen
the product theorem.

Grass therefore rejects both extremes. A precious specification file need not
contain process queues, worker identities, register layouts, or replacement
strategies merely because one proof uses them. Conversely, a bare declarative
predicate followed only by a monolithic assembly-to-predicate proof throws away
the reusable high-level correctness result. Operational definitions and their
lemmas may live in replaceable `Model` or `Process` modules; their exported
platform-independent satisfaction theorem remains a first-class input to the
final certificate.

“Replaceable” does not mean ignored. A selected assembly source is an exact
identity claim: the instructions, macros, register choices, literal operands,
containment policy, and layout which were authored are those erased, encoded,
linked, loaded, and decoded. Behavioral equivalence alone cannot substitute a
different implementation.

“The specification is precious” means it is minimized aggressively. Worker
counts, buffering, scheduling, allocator choice, register allocation, API call
order, and process topology stay out unless the product observes or constrains
them. Safety, required progress, terminal behavior, externally visible resource
policy, and genuine isolation/cancellation requirements stay in even when they
make an implementation harder.

Implementation models sit between those poles. Stable sort, B-trees, CRC,
DEFLATE, parsers, allocators, schedulers, TLS state machines, page tables, and
rendering algorithms should prove their core mathematics once. Many literal,
SIMD, generated, or hand-optimized assembly implementations can then establish
representation/control refinement to the same model. Novel assembly remains
free to select another proved model or pay for a direct extensional proof.

## 5. Proof economy and credible automation

Grass measures proof economy by author effort, diagnostic quality, rebuild cone,
kernel-check cost, and how often a purported library requires bespoke proof
engineering. Moving boilerplate into an opaque tactic which an expert must
repair for every new program is not a library win.

[PROOF_FEASIBILITY.md](PROOF_FEASIBILITY.md) gives the constructive proof sketch,
required caller inputs, falsification fixture, and fallback for mechanisms which
have been challenged as implausible. A bare theorem name is not accepted as a
feasibility argument.

Automation commitments are deliberately bounded:

- `SequentialAdapter` does not infer a process decomposition or correctness
  proof from an arbitrary relation. It normalizes a structured
  `DirectRelationalProgram` together with its `DirectProgramRealizes` witness.
  Standard specification constructors register reusable witnesses; novel
  programs supply one explicitly or author a process plan.
- straight-line assembly verification performs predictable forward symbolic
  execution over a decidable fragment. It does not synthesize loop invariants,
  discover heap separation, invent aliases, or guess provider contracts.
- verified assembly macros have transparent raw expansions and parameterized
  local theorems. They remove routine status, ABI, framing, copying, scanning,
  allocation, and loop ceremony without preventing literal replacement.
- typed whole-element copies infer initialization/occurrence transfer from exact
  footprints. Overlap, type punning, and novel layouts leave explicit goals.
- standard loop combinators may discharge arithmetic automatically, but the
  loop still declares its invariant and decrease/frontier law.
- concurrency libraries provide process/channel/resource invariant combinators;
  novel shared-state algorithms still state the interference and ownership facts
  that make them correct.

Routine ABI mechanics may be derived from a declared frame or supplied by a
transparent call macro. A bare authored `call`, however, is never silently
rewritten to insert shadow space, spills, argument moves, or cleanup. Such a
rewrite would make the emitted assembly cease to be the assembly the author
reviewed. The scalable compromise is explicit macro invocation, visible exact
expansion, local ABI proof, and unrestricted replacement with literal
instructions.

Every claimed automation path needs golden author-surface fixtures, adversarial
negative cases, residual-goal allowlists, compile/cache metrics, and an escape
hatch to literal assembly plus explicit proof. Failure should expose a local
typed goal, not time out in unbounded search.

## 6. Resource and lifecycle scale

Large systems are not one-shot CLI programs. The core model therefore treats
allocation, reuse, arenas, pools, descriptors/handles, threads, sockets, GPU
objects, pending work, and obligations as compositional resources over process
state and channel escrow.

Theorems can bound a process and all dynamic descendants on any resource axis:
resident bytes, virtual bytes, stack, Unix file descriptors, Windows handles,
sockets, threads, GPU memory/objects, pending records, or products of these.
Capacity credit makes backpressure part of reachability rather than an
assumption. Scope flux accounts for resources entering, leaving, being shared,
or surviving termination/restart.

Terminal process adoption is one explicit disposition for one-shot programs; it
is not the general memory-management strategy. Long-lived acceptance requires
deallocation, arena reset, pool return, cache eviction, generation change, or
another proved recycling policy. The memory model supports pinned interior
pointers and offset rebasing across generative reallocation so real data
structures do not depend on process exit.

## 7. What the spikes mean

The five spikes are architectural pressure tests, each with an intentionally
declared product scope:

- Hello validates the entire source-to-Win32-PE theorem chain. Its synchronous-
  stdout profile is an architecture-validation artifact, not the production
  general Windows console provider.
- In-memory sort validates allocation failure, stable algorithm refinement,
  dynamic vectors, partial byte I/O, and output barriers. It is not the final
  external-memory/locale sort product.
- Fixed-Huffman gzip validates a bounded streaming codec and round-trip model.
  A complete reusable zlib/DEFLATE library still needs dynamic Huffman,
  decompression, policy/tuning, and their model/assembly refinements.
- cleartext HTTP/2 validates process population, multiplexed logical streams,
  connection-local HPACK ordering, cancellation, partial byte streams, two-level
  flow-control backpressure, error scope, and multidimensional resource bounds.
  TLS and production deployment hardening remain outside the spike profile.
- The cube validates Win32 events, a long-lived reactive loop, Vulkan resource
  typestate, input, and composition of x86-64 plus SPIR-V in one exact artifact.

No limitation in one spike becomes a universal Grass limitation. Conversely,
the corpus must not call a narrow spike a general implementation. Product scope
and provider applicability appear in the specification/plan and artifact
metadata.

The spikes are not allowed to buy easy proofs by making their declared product
false. Within its named profile each artifact must be something we would ship
for that scope: exact bytes, honest applicability constraints, exhaustive
failures, required cleanup, and no unstated favorable environment. A spike may
deliberately omit general inherited-overlapped console support, external-memory
sorting, alternate compression formats, TLS, or device-loss recovery only when the
specification and artifact metadata say so. Later scale milestones must exercise
those omitted mechanisms; prose may not quietly turn a narrow milestone into a
general product claim.

In particular, process-exit adoption is valid proof evidence for an explicitly
one-shot CLI profile, but it earns no credit toward the long-running-system
gate. A game, database, server, or kernel subsystem must prove steady-state
reclamation, bounded retention, or a named growth policy over arbitrarily long
executions.

## 8. Large-system acceptance gates

Before Grass can claim readiness for its target systems, representative
milestones must demonstrate:

- separate compilation and library exports with stable ABI, ghost-state, memory,
  obligation, progress, and resource contracts;
- long-running allocation/reclamation and generation-safe stale-reference
  rejection without process-exit cleanup;
- synchronous, readiness-based, completion-based, callback, interrupt, and
  device I/O through one asynchronous byte/event model;
- bounded and unbounded dynamic process populations with cancellation,
  supervision, restart, and whole-subtree quantitative theorems;
- complex banked models such as dynamic prefix codes, tree/index structures,
  transaction/log recovery, page tables, or render/resource graphs;
- authored scalar/SIMD/atomic/hot-loop alternatives proving local equivalence;
- multi-ISA and multi-artifact composition;
- hierarchical builds whose measured work follows the semantic invalidation
  cone at repository scale; and
- adversarial model validation against cited CPUs, APIs, loaders, devices, and
  external libraries.

The scale claim is tested by the structural, graph-simulation, and calibrated
real-build ratchet in [OLEAN_SHARDING.md](OLEAN_SHARDING.md), not by manufacturing
an arbitrary number of instructions. For a one-leaf edit which preserves its
exported boundary, zero sibling certificates may be re-elaborated or
kernel-rechecked, only the changed shard and its hierarchical composition path
may be recomputed, and unrelated specification/provider certificates must be
untouched. Full source hashing and final artifact emission may remain linear in
bytes and are reported separately. Interface changes are measured against their
explicit semantic dependent cones.

They must also demonstrate that these mechanisms coexist in one nontrivial
system. Passing each feature in isolation is insufficient if their composition
causes global proof obligations, rebuild explosions, or a second semantic route.
Scale evidence records author annotations, unresolved proof goals, kernel-check
work, peak build memory, cache reuse, and mutation impact cones. Line ratios are
diagnostic smells, never acceptance axioms.

The first five spikes establish the baseline shape. They are not evidence by
themselves that these large-system gates have been met.

## 9. Decision rule

When proof economy for a tiny program conflicts with a single scalable theorem
architecture, prefer the scalable architecture, then remove the tiny program's
author-facing ceremony with transparent libraries and generated witnesses.
When an abstraction cannot be implemented predictably, cached locally, tested
adversarially, or explained through a small typed interface, narrow the claim or
redesign it. Do not create a semantic fork, weaken the final theorem, or move the
same bespoke work into a library and call it automation.
