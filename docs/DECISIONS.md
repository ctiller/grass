# Ratified design decisions

This file records decisions already accepted for the initial implementation.
Normative owners take precedence if wording is later incorporated there.

Spike-driven revision, 2026-09-01: the six refinement acts are ordered proof
concerns, not a mandatory sequential storage pipeline. Generated lowering and
first-class authored assembly are equal routes from a realized platform
contract. Basic-block entry/exit contracts are the reusable local proof
boundary. This preserves the proof ordering without forcing authored assembly
to imitate compiler-selected storage or CFG structure.

1. `emitProgram : VerifiedProgram spec -> ByteArray` is the verified gate.
2. Functional refinement and platform/ISA safety are separate certificate fields.
3. Normative execution semantics is relational; an oracle-driven runner selects
   replayable modeled executions and proves soundness. `PermittedExecution`
   means the conforming member of the modeled-execution partition.
4. Safety is universal over finite prefixes; progress, productivity, conditional
   termination, and unconditional termination are separate demands.
5. Reactive CFG cycles must decrease or universally cross a law-bearing frontier
   that transfers agency or has an independent specification-productivity proof.
6. Requirements are separate theorem demands and remain separated when possible.
7. Ghost-bearing operations lower through proved erasure to an unsafe raw layer.
8. Operations and obligations use existential packaging for open extensibility.
9. Memory uses generative hierarchical provenance, shadow pointer provenance,
   initialization, permissions, and a sealed access chokepoint.
10. Pointer recovery from integers and provenance preservation by untyped copies
    require additional proofs; typed operations may supply them automatically.
11. Borrow sharing uses authoritative unique loan identities; counts are derived.
12. Ordinary conflicting parallel writes are prohibited; atomics and ordering are
    separately modeled.
13. Obligations have explicit terminal dispositions, including unknown/abandoned
    failure where the specification permits it.
14. Provider demands use typeclasses projected from an explicit provider
    environment; the platform plan retains the exact dictionaries used upstream
    and ghost-propagates their identities.
15. The initial ISA is a dual-cited common x86-64 intersection with Intel and AMD
    refinements and separate validation.
16. The initial platform profile is Win32 x64 with Windows 10 as API baseline and
    documented APIs rather than direct syscalls.
17. The initial artifact is ASLR-enabled PE32+ with abstract RIP, relocations,
    derived imports, standard permissions, and unwind metadata.
18. Windows loading is an abstract proved transition including IAT patching; the
    actual loader remains a tested platform trust item.
19. Every writer has a reader and proves writer round-trip plus canonicalization
    for accepted inputs. Format-specific connection properties are additional.
20. Exact x86 syntactic round-trip may be weakened to semantic encode/decode
    equivalence when exactness harms instruction reasoning.
21. All instruction/API behavior has vendor/standard citations, review anchors,
    fuzzers, probes, and a per-profile trust ledger.
22. External libraries are trusted implementations only behind fully modeled and
    tested boundaries.
23. Proofs use the kernel; `native_decide` is prohibited and execution is not a
    proof. Universally quantified `bv_decide` is allowed.
24. The final certificate proves loaded behavior inclusion from the exact emitted
    bytes back to the ghost program across finite/infinite executions and faults.
25. Foundational extension points are versioned and migration-proved; version 1
    is tested against known targets but is not promised permanently sufficient.
26. Pure `Vec α` is the fundamental finite ordered array and `ByteArray` is the
    early public name for `Vec Byte`; physical `OwnedVec` carries distinct
    allocation identity and proves `Represents` rather than sharing extensional
    equality with the logical value.
27. Every verified artifact proves non-vacuous loadability for all admissible
    execution-context/base/import triples. The context, base, and import domains
    each have a separately named independent inhabitant; tuple inhabitation may
    not define one domain in terms of another. Every loader result is a valid
    initial state for the exact context. Every profile proves nonempty execution
    and response-or-pending domains.
28. Environment-contract violations receive assurance only through the maximal
    matched safe prefix before the first violation; no post-violation functional
    or cleanup claim is made.
29. Physical vectors separate stable `vecId` from generative `bufferId`;
    reallocation preserves the former and existentially returns a fresh latter.
    Capacity, allocation failure, mutable loans, and provenance belong only to
    `OwnedVec`, never pure `Vec`.
30. Every valid initial state has a modeled execution; a terminal initial state
    contributes an explicit zero-step conforming execution with its result and
    terminal resources.
31. Verified theorems receive a transitive axiom audit across all dependencies;
    only exact reviewed Lean logical-foundation constants are allowed.
32. Standard-library dependencies are stratified as `Core -> Std.Logical ->
    Semantics/Memory/Obligation -> Std.Owned`; lower ownership models never
    import their physical container specializations.
33. Conditional `environmentResponsive` has a fixed specification-level meaning.
    Each selected provider plan supplies an inhabited coherent concrete
    provider/scheduler strategy, projects its abstract branching strategy, and
    proves a refinement coupling their complete compatible-history sets;
    separately inhabited assumptions or an uncoupled function are insufficient.
34. Abstract terminal-status providers prove preservation, reflection,
    distinguishability on the demanded subset, and terminal/resource fidelity.
35. Runtime containment after an environment-contract violation is an explicit
    assembly implementation policy. It is not required for the conforming
    theorem and may be omitted by an optimized implementation.
36. Standard total outcome/status policy builders and CFG slice-consumer
    invariants own routine proof ceremony while leaving policy distinctions,
    registers, loop measures, and arbitrary custom assembly author-controlled.
37. Responsiveness is universal over every maximal continuation compatible with
    a coherent branching strategy. Concrete/abstract strategy refinement couples
    complete generated-history sets; one favorable history is insufficient.
38. Post-environment-violation containment requires a result-indexed typed return
    envelope proving exactly the surviving ABI, memory, loan, and frame facts.
    Arbitrary memory/control/ABI violations have no typed continuation.
39. Terminal reflection is program-relative: it ranges only over events
    independently reachable from the specification's demanded terminal requests,
    not every status supported by a reusable provider.
40. Spike programs separate a functional architecture milestone from broader
    product profiles. Spike 2 is explicitly an in-memory, bytewise, LF-normalizing
    stable sort for a declared I/O provider; external spilling, locale collation,
    stderr diagnostics, and adaptive overlapped Win32 I/O are product extensions,
    not facts hidden to shorten a proof. Each extension should preserve the
    minimal portable core when its semantics permit that reuse.
41. Physical struct layout is a reviewed construction choice. Standard layout
    machinery derives offsets, sizes, bounds, and representation lemmas, but it
    neither hides memory-footprint choices nor generates an assembly author's
    loads, stores, and indexing strategy.
42. End-to-end spike documents flow completely through their machine-language
    artifacts and exact emission. Contracts remain essential proof boundaries,
    but cannot replace undisplayed assembly helper bodies; a proved macro is
    acceptable only when its transparent expansion is present and auditable.
43. Infinite-pending existence belongs to the unrestricted execution/profile
    adequacy theorem used by universal safety. Adequacy of a strategy assumed
    responsive requires a nonempty rooted total strategy tree and maximal
    executions, but does not require that tree to retain a perpetually pending
    branch that would contradict universal settlement.
44. Portable programs use a small process-machine abstraction: pure logical
    state transitions consume typed external/correlated-response events and
    produce occurrence-free abstract demand multisets, finite logical observation
    segments, and an optional pure desired-view facet. Observation history is
    not duplicated in process state. Demand identities, routing, order, batching,
    and scheduling belong to the replaceable realization.
    Only verified driver commit transitions affect platform resources or append
    physical observations. This is React-shaped proof economy, not a model of
    React runtime semantics.
45. The primary portable model is a process topology and logical state ownership
    graph during realization: process kinds/instances, local state, explicitly
    shared regions, spawn/cancel/supervision relations, and typed event channels.
    Only the resource-parameterized portable specification function is precious
    program identity; it may contain abstract spec-process protocols. Selected
    resource models, realization protocols, their proofs, and the exact
    `ProcessPlan` weave are reviewed
    replaceable construction inputs which prove those contracts. External or
    independently pending API/library computations are child process protocols;
    frontier-free serial functions remain local Hoare calls. Callbacks, monadic
    sequencing, and parallel weaving are compositions or realizations of this
    one model.
46. Process channels carry Hoare-style send/receive contracts over sender,
    receiver, shared logical state, message occurrence identity, ownership, and
    obligations. Send places the exact occurrence and transfers in stable
    in-flight escrow with one affine resolve token. Receive or disposition may
    consume it at most once; unrestricted pending may retain it forever, and
    eventual resolution requires named progress assumptions. They are the high-level peer of typed CFG edges; platform queues,
    callbacks, API completions, synchronization, and direct control flow must
    refine their exact pre/post transfers.
47. `ProcessSpec` emits occurrence-free abstract demand sets, not command DAGs.
    Fresh identities, dependency order, batching, routing, supervision, and
    cancellation mechanism belong to the replaceable process realization.
48. Grass has one process algebra, not separate sequential and concurrent
    semantics. Sequential relational programs are normalized by a proved
    `SequentialAdapter`; explicit plans use the same `ProcessRealization` and
    driver theorems. The adapter plan is generated, inspectable scaffolding and
    is absent from the small-program author surface.
49. A proved process network can be flattened behind one process protocol and
    registered fractally as a child of another network. Flattening the canonical
    sequential adapter round-trips up to complete execution bisimulation.
    Physically serializing a genuinely concurrent plan additionally requires a
    `SerializablePlan` scheduler/commutation/progress proof.
50. Independence and syscall-trace commutation are proved before flattening.
    Disjoint process/channel/obligation footprints and commuting provider/
    observation effects yield a diamond; physical traces which linearize the
    same process partial order are strongly equivalent.
51. Partial I/O is modeled through asynchronous ordered byte-flow protocols.
    Positive reads produce nonempty chunks; positive writes commit exact prefixes
    and retain the unique suffix. Rechunking is irrelevant only under the named
    completed functional projection and for `ChunkExtensional` consumers;
    capacity, timing, resource, partial-prefix, and cancellation cuts use a
    stronger mapped relation. EOF, pending/readiness, failure, cancellation, and
    close remain distinct. Blocking and asynchronous APIs refine this same model.
52. Process plans support compositional quantitative theorem extraction. Resource
    metrics account for local state, shared regions, dynamic descendants, channel
    escrow, obligations, and physical layout. Capacity credit is affine channel
    state, so proved finite memory bounds force backpressure instead of assuming
    it. Metrics are not memory-specific: file descriptors, handles, sockets,
    threads, GPU resources, pending work, obligations, and products of axes use
    explicit sum, maximum, shared-once, or transfer composition laws.
53. A standard specification constructor may expose one uniquely selected
    `StandardSequentialRealization` through exact lookup in a named closed
    registry, allowing `verify_assembly plan with source` without
    application-maintained relational scaffolding. This is recorded
    proof-strategy inference normalized into the universal process algebra;
    provider selection remains explicit, absence or ambiguity is rejected, open
    typeclass priority is prohibited, and novel relational programs retain an
    explicit `using` form.
54. `VerifiedProgram` retains exact source elaboration, exact ghost erasure, and
    exact raw-instruction encoding witnesses before artifact representation.
    First-class authored assembly is an identity claim in addition to a
    behavioral refinement claim.
55. Serialization bisimulation is justified only by an execution-complete
    relational serial scheduler in both directions, including every result,
    lifecycle, maximal execution, observation, and obligation behavior.
    Conditional fairness is separate; overlapping operations require explicit
    linearizability. A deterministic scheduler normally proves refinement only.
56. Process-run semantics owns a linear outstanding abstract-demand bag.
    Realization-private occurrences erase bijectively to its live multiplicity;
    results and interruptions consume exactly one item and terminal states
    classify every remainder. Internal child occurrences are parent-local and
    only selected root occurrences project to the driver boundary.
57. Nominal identity freshness ranges over a monotone execution-prefix history,
    not the current live set. Resolve tokens are owned escrow assertions.
    Ordinary success/failure/termination and close are explicit lifecycle
    transitions distinct from death.
58. Resource bounds are reachable-state invariants over an owned resource
    algebra. Scope extraction includes lineage and temporal boundary flux;
    composition requires explicit disjointness, overlap attribution, phase
    exclusion, and cross-edge equations. Channel credit charges positive slots,
    payload and physical records and transfers retained payload cost to receivers.
59. Certificate lookup uses a Merkle locator over normalized theorem type,
    transitive semantic facets, profile, verifier/generator, toolchain/kernel
    options, and axiom-audit policy. Applicability is then kernel-checked against
    actual canonical content, theorem types and imported declaration identities;
    hashes are no logical evidence. Manifests compose hierarchically from measured
    shards; leaf work is proportional to Merkle depth and impact cone.
60. Reusable algorithm correctness is banked at an explicit Lean implementation
    model boundary, with a separate exact assembly/representation refinement.
    Custom assembly may refine that model, another proved model, or deliberately
    pay for a direct extensional proof.
61. Grass optimizes its theorem architecture for large, long-lived systems:
    games, databases, operating systems, compilers, graphics and storage engines.
    Bounded generated/internal ceremony for trivial programs is acceptable when
    it preserves one scalable composition law; author-facing routine ceremony
    remains a proof-economy defect to remove transparently. Spikes are pressure
    tests with declared product scope, not the project's objective function.
62. A terminating serial function with a local Hoare/footprint/obligation/
    resource contract may be called directly inside a process transition and
    realized by an ordinary ABI call. It does not become a child process merely
    because it is a call. External entropy, pending, independent cancellation,
    custodian transfer, or observable interleaving crosses a process frontier.
    A suitably serialized frontier-free process graph may export the same kind
    of callable contract.
63. Specification guarantees are a finite keyed family of independent theorem
    demands with explicit semantic dependency facets. Grass rejects a fixed
    four-bucket correctness tuple: functional, memory, concurrency, liveness,
    resource, obligation, applicability, diagnostic, and artifact demands have
    different composition laws, and future axes must be extensible without a
    semantic fork.
64. Cube rotation is a function of portable monotonic elapsed time and a
    specified angular velocity, not frame count. The Win32 realization samples
    `QueryPerformanceCounter` through the selected clock provider; refresh rate,
    coalescing, and GPU latency may change which frames appear but not angular
    velocity.
65. A disputed library mechanism requires a constructive proof sketch naming
    caller premises, induction/simulation cases, automation boundary,
    falsification fixture, and fallback. `PROOF_FEASIBILITY.md` owns these
    arguments. Neither “standard” nor “proof fantasy” is a sufficient verdict.
66. A certified assembly macro is a separately checked sub-CFG whose theorem is
    indexed by its exact transparent expansion. Parent modules may retain the
    invocation plus expansion identity and consume the contract; audit tooling
    must make the expanded raw listing available, but need not textually inline
    it into every parent Lean module. A bare call or instruction sequence is
    never silently rewritten.
67. Performance numbers, throughput ratios, GPU utilization, build-memory
    projections, and invalidation latencies require reproducible measurements on
    identified artifacts and hardware. Uncited estimates neither justify an
    architecture change nor excuse a poor implementation. The first five spikes
    establish proof shape; optimized scalar/SIMD, IOCP, multi-frame, and dynamic
    codec realizations are required later scale milestones and refine the same
    specifications where their behavior matches.
68. A policy is precious exactly when changing it changes admitted product
    behavior or a demanded guarantee. Exact output bytes, silence on resource
    exhaustion, connection admission bounds, deadlines, and fixed-after-ready
    storage may therefore be precious. OS worker count, polling/completion
    mechanism, buffer layout, and provider diagnostic codes remain replaceable
    unless separately observed.
69. Product correctness is proved at the portable specification/model level and
    reused by concrete realizations. Assembly proves an adjacent refinement to
    that already-proved model, and exact emission connects the resulting source
    to loaded bytes. Grass rejects a “zero proof at specification level” rule:
    operational state may move out of the precious `Spec` module, but eliminating
    the platform-independent satisfaction theorem would duplicate product
    reasoning across implementations and make local optimization globally
    invalidating. Direct assembly-to-specification proofs remain an explicit
    first-class escape hatch for novel implementations, not the default shape.
70. The configured program boundary is tripartite with a directed dependency: a
    reviewed selectable resource model is a parameter to the precious portable
    specification function, and a faithful target projection consumes the
    resulting instance. Grass rejects the inverse `ResourceContract behavior`
    shape. Microcontroller and data-center models instantiate the same program
    definition; exhaustion, admission, backpressure, and lifecycle behavior are
    explicit in each instance. Resource theorem keys and invalidation facets
    remain independent. The reviewed replaceable projection
    maps abstract observations, outcomes, capabilities, and provider demands to
    one coherent platform/API/ISA profile; it must prove preservation and may
    not weaken product policy. It becomes precious only where the product
    explicitly promises the target representation itself.
71. The process lens is the canonical causal and compositional proof model, but
    its private operational state belongs to a replaceable Act 1 model/process
    module rather than the precious specification function. It exports a small
    portable satisfaction/boundary theorem connecting every observation to its
    generating transition. Serial functions and basic blocks refine individual
    steps through local Hoare/CFG contracts. Concurrent weave invariants are
    independent frameable families; an aggregate closing record is a thin
    facade, not one monolithic induction reopened by unrelated changes.
72. Resource models are explicit values with stratified, law-bearing typeclass
    capabilities, not one closed universal record and not ambient provider
    selection. Each specification quantifies over only the axes and bounded
    customizations it needs; domain-specific classes may add file descriptors,
    pages, interrupt work, GPU objects, or other axes. The specification depends
    on that resource value, while the selected platform later proves it realizes
    the exact value and laws used upstream.
73. The precious root `SpecProcess` captures one composable suite of semantic DSL
    fragments into its one transition/observation contract, not an execution
    topology. `VerifiedProgram` is indexed by that exact root process.
    Relational, stream, trace, grammar, protocol, temporal, resource, and domain
    forms are authoring fronts which elaborate through explicit typed junctions.
    A replaceable `ProcessPresentation` may
    then provide abstract protocol roles, typed channels, linear/shared logical
    state, and causal laws together with an exact-denotation theorem. Serialized,
    reactor, worker-pool, callback, and device presentations may all serve the
    same specification; changing among them cannot change the precious value.
74. Refinement acts apply locally and fractally, not as whole-program phase
    barriers. A typed refinement lens may replace one role/subgraph while
    preserving its observation causality, channel, custody, obligation,
    resource-flux, and progress boundary and framing all nonselected processes.
    It may introduce a finite requirement delta. Subsystems may therefore sit at
    different abstraction depths—such as Vulkan graphics beside abstract disk
    I/O—until later local proofs lower them. `VerifiedProgram` closure requires
    all frontiers discharged and one coherent accumulated provider environment.
75. `ProcessRealization.blend` composes independently refined and still-abstract
    spec-process roles at exact exported boundaries. A subsystem certificate
    seals its portable implementation while exporting
    refinement, requirement delta, observation causality, custody, resource, and
    progress facts. Mixed graphs support parallel proof construction but are not
    emittable. Execution requires a proved realization, including for mocks;
    `VerifiedProgram` accepts only a complete coherent portable blend followed
    by an exact post-projection machine blend covering every closed scope.
    Machine artifacts never appear before the platform/ABI/ISA environment
    exists and cannot disappear before the final machine certificate.
    Cross-subsystem
    reuse is mandatory when a changed implementation preserves its boundary,
    not when the boundary itself changes.
76. The resource value is explicit at precious specification construction and
    becomes an implicit dependent index downstream. Thus an author writes
    `def spec : SpecProcess resources := ...` and later
    `VerifiedProgram spec`, not a second ambient resource selection. Resource
    typeclasses expose bounded construction operations and laws; the resulting
    exact semantic dictionary is captured in `spec`, never reselected
    downstream, and no resource class chooses a platform provider.
77. Relational, stream, trace/reactive, grammar, protocol, temporal, resource,
    and domain syntax are first-class authoring fronts captured into one root
    `SpecProcess`, not independent semantic towers. Sort and gzip use
    relational/stream/grammar-shaped meaning without invented pipeline actors;
    interactive and multiplexed systems may demand abstract session contracts
    without freezing a decomposition. Every front end feeds the same
    refinement and exact-artifact theorem.
78. Resource capability typeclasses are construction-time builders. A
    root `SpecProcess` snapshots the exact finite, uniquely keyed semantic
    dictionary used to construct it; all downstream proofs project from that
    value. Competing lawful instances over the same carrier cannot lend limits,
    deadlines, exhaustion, or lifecycle facts to the selected `spec`.
79. Local well-founded ranks do not replace infinite reactive semantics. They
    rule out unbounded internal stuttering between visible steps; productive
    coinduction, divergence reflection, explicit environment frontiers, and a
    concrete-to-abstract fairness projection establish maximal infinite
    behavior. An inductive OS-settlement premise alone would silently assume the
    liveness fact being proved.
80. The multi-file spike corpus is an audit fixture, not a mandatory per-program
    authoring ceremony. Public closing syntax may co-locate resource selection,
    projection, plan, assembly, and emission and generate closure/artifact
    certificates. Physical modules are selected by measured elaboration and
    caching boundaries; neither one file per basic block nor a fixed three-file
    layout is normative.
81. Optimized assembly is a required acceptance axis. Scalar reference models
    remain useful, but SIMD, carryless-polynomial, atomic, and other tuned
    kernels must be able to prove local extensional step equivalence using
    kernel-checked reflection such as `bv_decide` or separately checked proof
    certificates. An optimization does not need to adopt a compiler-like DSL;
    literal instructions and transparent parameterized macros remain peers.
82. Long-running spikes must prove resource recycling and steady-state bounds,
    not rely on process-exit adoption. Rings, generational pools, arenas, and
    ordinary alloc/free chains are library candidates rather than a closed
    allocator trinity. Each selected realization proves its own infinite-trace
    conservation and terminal disposition against the resource axes demanded by
    its specification.
83. Grass mines Erlang/OTP for typed signal order, selective receive,
    correlated calls, monitors, links, supervision strategies, restart
    intensity, postponed events, timeout races, and explicit version handoff;
    it does not adopt BEAM execution semantics. Ordinary terminal safety stays
    in the base process proof; cancellation, bounded shutdown, restart, and
    upgrade promises attach opt-in typed termination facets naming safe points,
    causes, custody disposition, cooperative progress premises, and escalation.
    “Let it crash,” unbounded
    mailboxes, scheduler reductions, and arbitrary forced thread death never
    discharge safety, resources, or obligations.
84. Cancellation policies form an optional compositional algebra. An ordinary
    serial function is an uncancellable segment with no extra author field;
    cancellation points and interruptible calls are explicit combinators.
    Sequencing conserves a pending affine cancellation occurrence and computes
    safe points, delay premises, and terminal custody. Branches weaken to common
    guarantees, loops require a point on every fair continuing cycle or an
    independent termination proof, and flattening preserves the summary. Thus
    `uncancellable |> cancelpoint |> uncancellable` has a derived policy, while
    a forever-blocking segment cannot falsely acquire eventual cancellation.
85. Text and binary languages are precious through a typed `Format` denotation,
    not through a parser algorithm or process graph. A format distinguishes
    complete derivation, repairable incomplete prefix, and irrecoverably invalid
    prefix; states semantic values and explicit ambiguity/disambiguation; and
    supports binary lengths, bits, refinements, and productive recursion.
    Parsers and writers are replaceable realizations with soundness,
    completeness, exact residual-input, and round-trip laws. Stateful protocol
    legality remains a separate precious transition relation connected to the
    decoded values.
86. Specification authoring is an open family of typed DSLs sharing
    `ContractFragment` and `SpecJunction`. The authored fragment values and
    meaning-bearing junctions are precious; their composed denotation is the
    single contract consumed by `VerifiedProgram`. Execution assignment to
    processes, callbacks, buffers, APIs, CFGs, or instructions is a replaceable
    presentation/realization. New DSLs must provide total denotation,
    composition laws, conflict diagnostics, adversarial fixtures, and a direct
    Lean proof escape hatch without creating another correctness tower.
87. A DSL may introduce a precious existential `ProcessRequirement`, such as “a
    process realizing this parser format.” The enclosing root `SpecProcess`
    proves behavior parametrically using only that exported contract. Refinement
    supplies a witness—one process, a captured subgraph, generated code, or raw
    assembly—and proves it acceptable. Ambient instance selection after spec
    construction and dependence on the witness's private topology are forbidden.
88. Lean is a Turing-complete assembly construction language, while the kernel-
    checked result remains exact first-class assembly. Typed object/stack layouts
    compute named offsets and prove alignment, disjointness, representation,
    ABI, and unwind laws. Transparent generators may emit short verified
    instruction fragments for prologues, calls, spills, field access, and other
    routine work. Literal instructions and numeric offsets remain legal with
    local proofs. Logical block invariants use a separate physical `Placement`
    unless register identity is intentionally part of the contract; annotation
    predicates elaborate as Lean terms, never untyped strings.
89. Grass's maintained spikes use concise typed construction syntax because
    they are permanent copy sources. Named layout paths replace hand-computed
    object, frame, ABI-home, and bitfield displacements; transparent ABI and
    instruction-burst constructors replace bookkeeping where they preserve an
    obvious expanded view. Raw offsets and entirely literal assembly remain
    first-class escape hatches and receive dedicated fixtures, but are not the
    ordinary exemplar spelling. Lean functions are the semantic macro system;
    assembly quotation and splicing are its readable surface, with authored,
    elaborated, and exact expanded views available to review.
90. A reusable assembly constructor exports a strong parametric theorem about
    the entire family of instruction sequences it generates, not merely an
    expansion equation. Its checked summary may include Hoare behavior, access
    and fault footprints, stack delta, preservation, obligations, resources,
    cancellation, unwind metadata, and citation coverage. Call sites instantiate
    and compose that theorem instead of re-deriving instruction proofs, while
    emission and review retain exact expansion. Hierarchical constructor
    certificates are therefore part of Grass's proof-size and incremental-build
    strategy; literal one-off assembly remains equally legal.
91. `withStack` is the concise typed surface for lexical addressable objects in
    assembly. It binds typed stack objects whose field projections elaborate to
    memory operands and whose proofs track layout, provenance, permission,
    initialization, loans, and non-escape. The binder supplies lifetime demands
    to an inspectable enclosing frame plan; it does not necessarily emit dynamic
    `rsp` adjustment. Nonoverlapping lifetimes may share physical storage, while
    pinned layouts, disabled reuse, explicit overlays, and entirely literal
    frames remain available to first-class assembly authors.
92. A one-line assembly tactic is acceptable only as a kernel-checked
    certificate consumer and deterministic dispatcher with a documented
    residual-goal boundary. It may instantiate fragment-family theorems,
    compose typed CFG contracts, and invoke checked decision procedures. It may
    not silently discover or choose invariants, algorithmic correspondences,
    failure policies, representations, or omitted provider cases.
93. Resource parameters are stratified into a precious-family
    `SemanticBudget` and a non-precious `ExecutionEnvelope`. The former contains
    only capacities, deadlines, backpressure, exhaustion, and bounds which
    affect admitted or observed product behavior. The latter contains workers,
    scheduling, handles/descriptors, concrete buffers/arenas, polling/completion
    policy, and platform reserve. `RealizesSemanticBudget` proves representation,
    capacity, backpressure, deadline, exhaustion, and lifecycle compatibility;
    changing an envelope does not change the root `SpecProcess`.
94. Large-system build locality uses `VerifiedObject ProgramSignature` and a
    verified modular linker beneath the final gate. A signature exposes only
    callable/process/observation/resource/obligation/provider/ABI contracts and
    may existentially hide a subsystem's private `SpecProcess`. The linker proves
    signature composition against the one exact root and returns
    `VerifiedProgram root`; the final program is not weakened to an existential
    signature index. Symbolic relocations isolate machine proofs from final
    layout, and hierarchical object certificates permit measured incremental
    reuse without promising constant-time relinking.
95. Assembly/source manifests and total CFG attribute maps are structurally
    derived from the same typed assembly AST; authors do not maintain parallel
    symbol, label, stack-object, constructor, or cancellation dictionaries.
    Generated manifests/listings may be committed outside the authored spike
    directory or embedded in its annotated document as checked review
    projections. Standard Program/Artifact closing records are likewise
    derivable bundles, while novel connection lemmas remain explicit.
96. `verify_asm` orchestrates separately callable checked elaboration, symbolic
    execution, spatial framing, arithmetic/bit-vector, ghost/resource, and
    closure phases. No phase performs open-ended cross-domain search; diagnostics
    name the exact instruction/edge and residual proposition. Reflection may
    compact proof terms but does not make evaluation constant-time.
97. Spike documents and spike source directories are distinct review views.
    `docs/SPIKE_N.md` contains authored code plus labeled generated expansion,
    proof sketches, and explanation. `Spikes/N_Name/` contains only what agents
    are expected to author and maintain. Every file there counts as ceremony;
    generated manifests, ordinary bindings, adapter witnesses, and artifact
    wrappers remain inspectable but do not receive authored files. Reviewers
    must cross-check both views mechanically and report author cost separately
    from generated/kernel cost.
98. Lean modules are the physical unit of proof invalidation. Each bounded
    machine shard has a stable signature module, a private exact implementation,
    an opaque checked certificate, and a serialized verified-object facet.
    Callers depend on imported signatures; bounded-fanout aggregate modules
    depend on certificates. Scale acceptance proves edit locality over this
    shard DAG, simulates large compact graphs, and calibrates representative real
    builds. Grass does not manufacture a million-instruction Lean term as a
    proxy for repository scale. See [OLEAN_SHARDING.md](OLEAN_SHARDING.md).
99. A banked implementation-model proof attaches only through an authored exact
    source scope and physical representation. The author selects entry and exit
    frontier, containment treatment, and any imported component calls; the
    elaborator derives occurrence coverage and rejects all other escapes. Common
    representation constructors may remove algebraic boilerplate but must expose
    every physical base, length, layout field, and result location. Whole-source
    `using_model` inference is rejected.
100. All design spikes share one future implementation ratchet: classified
    mirror, source closure, verification, artifact, first-failure mutation, and
    `.olean` locality reports with versioned schemas. Design approval requires a
    believable interface for those outputs, not fabricated runs. Implementation
    approval later requires the retained evidence in
    [IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md).
101. `.gobj` serializes only a proof-free first-order `GobjPayload`.
    `VerifiedObject` remains an opaque in-kernel value containing the exact
    payload and its source/machine/signature theorems. A cached file participates
    in verified linking only after parsing proves equality with that certificate's
    payload. Digests and certificate names are locators, never the bridge;
    `emitProgram` remains derived from the certified linked artifact.
102. Interactive rendering has an explicit conditional-productivity contract.
    While the application is running, visible, nonzero in extent, and has no exit
    request, continued frame opportunities plus scheduler, platform, and GPU
    responsiveness must eventually produce an accepted frame observation or a
    declared terminal outcome. Individual opportunities may coalesce, and no
    fixed cadence is promised; an enabled renderer may not stutter forever.
103. Process proofs use the same separate-compilation discipline as machine
    proofs. Large programs use module-local open registries, facet-indexed
    opaque certificates, scoped cancellation coverage, SCC summaries, and
    bounded-fanout aggregate DAGs. A closed whole-program process sum, global
    blocking-call equality, or witness indexed by the complete plan is rejected
    because it makes a local process edit a whole-program type change.
104. Spike proof-economy accounting prices theorem-shaped identifiers. Every
    referenced name is classified as authored, an exact parametric library
    instance, generated structure, or versioned authority-model work; unresolved
    names fail. Pre-implementation burden estimates are smell tests and are
    replaced by elaborator-produced residual-goal and proof-cost reports.
105. A typed x86 sequence-constructor language is not itself a raw instruction
    listing. Its implementation claim requires complete inspectable expansion,
    a theorem connecting the constructor to those instructions, and a literal
    same-contract override. Spike 4 carries representative fixtures and makes
    full HPACK expansion an implementation gate.
106. Product-defining constants and observable behavior remain visible in
    ground precious vocabulary. Spike 4 names its endpoint and client response
    theorem; Spike 5 names geometry, colors, angular velocity, and conditional
    productivity, and observations do not carry proofs of their own acceptance.
107. Cross-provider implementation coordination uses the orphan
    `refs/heads/agent-bus` branch. Each registered agent exclusively appends to
    segmented `<agent>/<six-digit-segment>.jsonl` logs with 1,000 events per
    segment. Events are immutable and causal; current scope, plan, progress,
    issue, dependency, handoff, and review state is derived by replay rather
    than stored in shared mutable files.
108. Every product change reaching `main` has at least one author agent and one
    distinct eligible reviewer agent. An author nominates the reviewer for a
    named product branch, which may continue advancing during review. The
    reviewer takes the nomination and either requests changes, declines, or
    personally merges a reviewed snapshot cleanly into current `main`. The
    receipt records the snapshot actually incorporated. There is no separate
    approval token returned to the author, and authors do not merge their own
    changes. Force pushes are forbidden on all protocol branches.
109. Every agent-bus identity has one immutable primary role: `implementor`,
    `reviewer`, `coordinator`, or `observer`. Product authoring and review/merge
    authority are deliberately separated between implementor and reviewer
    identities. Changing workload requires a new agent name rather than a role
    mutation, so dedicated review remains visible and mechanically checkable.
110. Reviewer silence, quota exhaustion, or provider loss never transfers
    authority implicitly. An author or bootstrap-authorized coordinator may emit
    `review.reassigned`, preserving the request and its open findings and
    requiring a different reviewer to accept. Only that reviewer may clear or
    explicitly supersede inherited findings. A published merge
    authorization remains an immutable candidate-specific verdict and can only
    win or lose its pinned product compare-and-swap. If a reviewer disappears
    after winning but before its receipt, a bootstrap-authorized coordinator may
    reconcile only the already-demonstrable product-history fact.
111. Product merge review is two-phase. `review.merge_authorized` pins the bus
    state, previous `main`, reviewed commit, exact conflict-free merge commit,
    passed checks, and reviewer before a non-force push. `review.merged` is the
    post-push audit receipt, not retroactive authority. Main always receives a
    reviewer-trailed merge commit, even where Git could fast-forward.
112. Agent-bus V1 has complete bounded schemas in `AGENT_BUS_SCHEMA.md`, a
    65,536-byte event-line limit, causal same-agent offline references, explicit
    work reassignment, deterministic scope-race defaults, validation CI, and
    malformed-log quarantine limited to unrelated diagnostic publication. The
    helper audits product history but, in the cooperative shared-credential
    model, does not claim it can prevent a direct push performed outside itself.
113. Bus-tree structural validity and product-object linked verification are
    distinct. Missing/unreachable remote objects make linked claims
    `unverifiable`, not malformed; authority-bearing operations still fail
    closed until fetch and verification succeed. Present mismatches are invalid.
114. Merge determinism is pinned by an explicit engine epoch. Reviewed
    `merge_engine.activated` events upgrade the fleet without rewriting bootstrap
    or historical authorizations. Each candidate names its epoch and uses fully
    deterministic commit metadata, with cross-platform object-ID fixtures.
115. `agent.resumed` may transfer exclusive custody from the identity's latest
    own lifecycle event of any status or a coordinator retirement targeting it,
    so silent death while `active` does not strand the identity or its role.
116. The specification/process boundary forms an acyclic diamond. A neutral
    `Specification` layer owns `DriverBoundary`, demand/result vocabulary,
    requirement keys, and other typed junctions imported by both sides.
    `Semantics` owns precious `SpecProcess` behavior; `Process` owns replaceable
    structural networks and execution machinery; `Refinement`/`Weave` alone
    relates a selected network trace to a `SpecProcess`. Neither `Semantics` nor
    `Process` imports the other merely to state its core objects. This records
    the ruling carried by agent-bus event `coord1:5`, originating at
    `c-process:4` and requested as dependency `c-process:17`.
117. There is one structural abstract process-network declaration. It is owned
    by `Process`, is generic over its protocol family, preserves the role-schema,
    instance, protocol, and composition shape used by the spikes, and contains
    no `BehaviorContract`, denotation, trace-denotation, or exactness field.
    `Semantics` may instantiate that structure inside the wrapper
    `ProcessPresentationNetwork`; this is not a second structural declaration.
    `ProcessPresentation` then selects an explicit trace for that wrapper and
    proves exact behavior and requirement correspondence. Neither the selected
    trace nor its exactness theorem is a field of `StructuralProcessNetwork`.
    This records `coord1:4`, originating at `c-process:3`, and names the wrapper
    consumed by the synchronized Spike 4/5 surface under dependency
    `g-design:23`.
118. Cancellation coverage is scope-indexed. One core `CancellationPolicy` is
    indexed by a scoped cancellation-point family and consistently names its
    discovered `blockingCalls`; `ScopedCancellationCertificate` ties both
    families exactly to a `ProcessScopeSummary`. Whole-plan coverage is the
    hierarchical composition of these certificates. A process-root spelling in
    authored syntax may infer its scope, but is elaborator sugar rather than a
    second Lean arity. This records `coord1:6`, originating at `c-process:5`.
119. `ProcessPlan` has only its declared registry and boundary parameters.
    The undeclared `ProcessNetwork` spelling is deleted. Root-oriented notation
    may construct or infer those parameters through typed elaboration but never
    denotes a second `ProcessPlan` type application. This records `coord1:7`,
    originating at `c-process:6`.
120. `EffectDemand boundary` abbreviates `boundary.Demand`, and
    `EffectResult demand` abbreviates `boundary.Result demand`. Protocol-specific
    operations enter through typed constructors of the open boundary demand
    family. `SequentialAdapter`, not the precious authoring type, generates
    occurrence identities, child bindings, and pending multiplicity. This
    records `coord1:8`, originating at `c-process:7`.
121. Interruption, logical-fault, and environment-violation classifications are
    open associated families of a selected `ProcessVocabulary`; Grass rejects a
    closed whole-program sum and an unclassified `other` fallback. A reusable
    network or protocol boundary selects the vocabulary once, so ordinary
    `ProcessSpec` authors do not restate three bespoke type fields. Delivery
    across different vocabularies requires a total typed classification or
    translation theorem; an empty receiving class is evidence that the route is
    unreachable, not permission to discard an event. This resolves
    `c-process:8` and ratifies the constrained form requested by `c-process:9`
    under acknowledgements `g-design:3` and `g-design:4`.
122. Cancellation and supervision are separately imported topology facets, not
    mandatory fields paid by every process. The weaker graph/population/spawn
    object is named `ProcessTopologyCore`. `ProcessTopology requirements`
    contains that core plus exactly the facet family demanded by the selected
    specification, with named aggregate theorems recovering every required
    cancellation and supervision contract. The unqualified `ProcessTopology`
    name may not denote a weaker value while prose assumes absent lifecycle
    authority. This resolves `c-process:10` under acknowledgement `g-design:5`.
123. Normative ratifications are durable product content, not bus-only state.
    `DECISIONS.md` records each accepted decision using stable numbering and
    cites the originating and ruling agent-bus event identifiers when applicable.
    Bus events retain routing, custody, and timing; this file owns the rule that
    implementations and normative documents must follow. This resolves
    `coord1:13` under acknowledgement `g-design:6`.
124. An open nominal metadata axis may use a closed carrier with an exact
    extension key such as `(owner, kind)` only when the value selects an
    identity and carries no fallback semantics. Consumers that need laws for an
    extension must resolve that exact identity through a typed registry and
    reject an unknown identity. They may not interpret `extension` as `other`,
    approximate it with default behavior, or use it to hide an unclassified
    event. This permits `RequirementKind.extension` as an invalidation and
    diagnostic facet; it does not weaken decision 121, because process faults,
    interruptions, and environment violations advance semantic state and remain
    typed per `ProcessVocabulary`. This resolves the classification part of
    `coord1:16`, raised by comparison of `c-process:8` with `g-foundation:4`,
    under acknowledgement `g-design:13`.
125. `Specification` names the neutral dependency layer below both `Semantics`
    and `Process`; it owns typed junctions, demand/result boundaries, and
    requirement keys, not precious behavior. The semantic root remains named
    `SpecProcess` and belongs to `Semantics`. Its defining source/module should
    therefore use the specific `SpecProcess` name rather than a generic
    `Semantics.Specification` name that suggests a second owner for the neutral
    layer. This resolves the terminology part of `coord1:16` under
    acknowledgement `g-design:13`.
126. A supplied fault plan selects what happens only if execution reaches the
    plan's fault-delivery point; it is not itself an architectural-fault
    occurrence. If an authority denial stops an operation at an earlier
    substep, or denies the planned faulting substep before fault delivery, the
    resulting state records the denial and the actually executed prefix but
    does not append the unreached fault. Retaining that fault would invent an
    event after the modeled execution had stopped. An observed hardware trace
    that asserts the later fault despite the earlier modeled denial is instead
    evidence that the trace and the admitted model/profile disagree; validation
    must report that discrepancy rather than combining both outcomes in one
    machine history. A tool may retain the offered plan in a separate attempt or
    oracle diagnostic, but it is not part of the architectural fault ledger.
    This resolves `c-mem:21` and makes the provisional M2 behavior normative.
127. Obligation-ledger transformation is indexed by the exact operation exit
    and is independent of memory-effect visibility. An operation that can
    complete, fault, interrupt, cancel, or commit partially declares, through
    its owning protocol theorem, the exact ledger transformation for every
    admitted outcome and the linearization point or staged points at which each
    transformation takes effect. A fault before such a point preserves that
    obligation fragment; a fault after it applies the declared transformation.
    Staged transformations require separate substeps or an explicit
    outcome-indexed relation. Grass may not infer ledger behavior from committed
    byte counts or from the delta constructor: always applying a discharge can
    leak a duty, while always preserving it can resurrect a duty whose protocol
    action already occurred; the analogous create cases are equally
    protocol-dependent. If a faulting outcome carries a ledger effect but has no
    declared fault rule, the operation/fault combination is rejected rather
    than assigned a default. This ratifies M2's
    `faultWithUndeclaredLedgerEffect` behavior as the fail-closed interim rule
    and resolves `c-mem:28`; a later outcome-indexed interface may admit the
    operation only with its complete protocol proof.
128. A process-network assertion is indexed by both its topology and an explicit
    world agreement; `NetworkAssertion topology` with no world is not a valid
    interface. `ProcessPlan` breaks the apparent recursive dependency by
    declaring its per-edge message family before its contracts. Topology plus
    that family defines `LogicalProcessNetworkCore`; the plan's channel
    contracts are then instantiated at the canonical agreement for that full
    logical world, and the public `LogicalProcessNetwork plan` is an
    abbreviation of the core. This is one network semantics, not a second
    topology-level escrow model: the core is only a construction seam. Lower
    reusable assertion and channel modules may remain polymorphic in an
    arbitrary `WorldAgreement`, but a completed plan must bind them to its full
    logical network. This avoids both a self-referential structure and an opaque
    escrow carrier weaker than `ChannelEscrowLedger`. It resolves
    `c-process:43` and replaces the unimplementable arity in `PROCESS.md`.
    Since assertion footprints remain arbitrary predicates, the canonical
    `agreesGlue` construction may use the reviewed `Classical.choice` constant
    already allowed by `FOUNDATION.md`; the transitive axiom audit exposes that
    dependency. Choice is localized to the logical-world supplier, while the
    generic assertion/framing library remains parametric and does not choose
    worlds. Grass does not impose decidable or finite footprints solely to
    remove an already-reviewed foundation constant.
129. `ProcessLifecycle` is indexed by the instance's `ProcessSpec` and every
    ending constructor stores the exact outcome it records: terminal result,
    cancellation reason, interruption reason, logical fault, environment
    violation, or process-death reason. A payload-free terminal tag is
    insufficient because `ProcessSpec.Terminal` is relational: one local state
    may admit multiple terminal results, so network state could not determine
    what a join returns or what the parent received. The same loss is immediate
    for fault, violation, interruption, and cancellation classes, which local
    state does not determine at all. Network well-formedness proves that the
    stored terminal result satisfies `Terminal request local result`; exact
    lifecycle transitions prove that the value stored in the child event,
    parent projection, and resulting instance tag is the same value; a typed
    death disposition likewise determines the exact stored death reason. This
    is generated transition bookkeeping, not an additional process-author
    proof field. It resolves `c-process:46` and supersedes the unindexed
    lifecycle field reprinted in decision 128's `ProcessInstance` surface.

## Explicitly rejected shortcuts

- bolting memory safety on after an instruction library exists;
- treating ghost streams and raw streams as peer verified representations;
- using one sharing count without loan identities;
- treating API failure as impossible or as an unconstrained no-op;
- choosing providers through ambient global instance search;
- calling Windows syscalls directly for the initial user program;
- disabling ASLR to simplify proofs;
- proving a semantic instruction list while emitting unconnected bytes;
- accepting undecodable indirect control flow as safe;
- relying on emulator/fuzzer agreement as proof;
- silently considering obligations discharged on process failure.
- restricting process graphs to physically concurrent code and allowing serial
  subsystems to end on a separate semantics. This would duplicate boundary,
  failure, liveness, obligation, and resource theories and make later parallel
  composition a rewrite. Serial CFG proofs remain local Hoare proofs, while a
  generated/cached adapter and proved serialization remove author and runtime
  ceremony without creating a semantic fork.
