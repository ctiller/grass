# Foundation and trust contract

## 1. Mission

The scale and proof-economy priorities of this mission are fixed by
[VISION.md](VISION.md). Grass targets large, long-lived systems such as games,
databases, operating systems, compilers, and graphics/storage engines. Small
programs test ceremony and the end-to-end chain; they do not justify a second
semantic architecture which would weaken composition at system scale.

Grass constructs executable programs by refining a high-level Lean
specification through a reviewed replaceable process plan and typed control-flow
graph into raw target instructions. It must prove that every permitted execution of the emitted
artifact:

- refines the passed specification under its declared observation projection;
- satisfies independently stated platform and ISA safety theorems;
- respects memory provenance, initialization, permissions, and race rules;
- satisfies ABI and CFG entry contracts;
- preserves, transfers, or closes every linear obligation lawfully;
- meets its declared progress and liveness contract; and
- is the same program connected to the serialized executable bytes.

Proof by running one execution is prohibited. Theorems over inputs, API results,
schedules, interrupts, allocation choices, and other entropy must quantify over
all permitted cases. `native_decide` is prohibited as proof authority.
`bv_decide` is allowed when it kernel-checks a universally quantified finite
proposition. Narrow point computations may be used only for genuinely closed
point facts.

## 2. Public and unsafe boundaries

The ordinary emission path is:

```text
domain specification DSLs + semantic junctions
  -> one precious root SpecProcess
  -> ProcessPlan with ProcessPlanRealizes
  -> verified process driver
  -> ghost-bearing verified program
  -> proved ghost erasure
  -> RawProgram
  -> Grass.Unsafe.emitRaw
  -> bytes
```

`emitProgram` is the public verified gate. `Grass.Unsafe` exposes raw parsing,
decoding, stepping, construction, and emission for model validation, fuzzing,
and unverified imports. The namespace and types must make the loss of assurance
visible. An unsafe value must not be implicitly promoted to `VerifiedProgram`.

The raw writer may have serialization proofs. “Unsafe” means that arbitrary raw
instructions carry no functional, safety, or liveness certificate.

## 3. Trust boundary

The trusted computing base is recorded per platform profile and contains, at
minimum:

- the Lean kernel and explicitly selected dependencies;
- the correspondence between formal models and vendor specifications;
- the correctness of actual CPUs, firmware, loaders, OS APIs, and external
  libraries relative to those specifications;
- any code extraction/runtime used to execute the byte writer;
- explicit profile assumptions describing external/model correspondence.

Every theorem used by the verified gate is audited transitively for axioms,
regardless of which dependency declared them. Only the reviewed Lean logical
foundation allowlist (`propext`, quotient soundness, and classical choice, with
their exact toolchain declaration names) is permitted. Dependency-defined axioms,
`sorryAx`, `sorry`, `admit`, unsafe declarations used as proof, and equivalent
admission mechanisms make the gate fail. External reality cannot be proved
inside Lean: it is exposed as a parameterized profile assumption and recorded in
the TCB ledger, not converted into a false closed theorem.

Grass must not hide trust in generated source, external assemblers, linkers,
emulators, FFI shims, undocumented behavior, or test results. External libraries
may be trusted implementations only after their boundary is modeled. Tests
challenge trust; they never establish a theorem.

## 4. Repository laws

1. No semantic invention: ISA/API behavior requires an authoritative citation.
2. No unconnected twins: proved models and emitted artifacts require a
   connection theorem.
3. No pointwise masquerading: examples and executions are not universal proofs.
4. No safety afterthought: every instruction/API model declares memory,
   concurrency, fault, interruption, and obligation effects when applicable.
5. No silent entropy: every external or nondeterministic result appears in the
   semantics and every proof handles all admitted values.
6. No ambient provider choice: a nominal platform plan selects coherent APIs.
7. No obligation disappearance: every terminal edge gives each obligation an
   accepted disposition.
8. No permissive fallback: unknown instructions, targets, effects, encodings,
   or API behavior are rejected, not approximated as no-ops.
9. No erasure gap: ghost removal is proved semantics-preserving.
10. No ratchet regression: every discovered model discrepancy becomes a test,
    theorem, restriction, or documented trust item.
11. No god files or proof duplication: semantic facts have narrow owners and
    consumers use their exported theorems.
12. No build extravagance: routine builds remain shardable and lightweight;
    multi-gigabyte generated states require a reviewed exception.
13. No private topology: published corpus and validation data contain no personal
    account paths, hostnames, device serials, or irrelevant workstation layout.
14. Proof locality: a change to a specification field, platform plan, or basic
    block invalidates only certificates that semantically depend on that change.
    Generated identities do not force orthogonal re-proving, and the build
    explains the invalidation cone.
15. No weave leakage: only the resource-parameterized root `SpecProcess` and the
    DSL components/junctions it captures are precious program meaning. It may
    demand semantic child-process contracts, but no selected role decomposition,
    process population, state partition, channel weave, scheduler, or physical
    topology. Presentations and realizations remain reviewed replaceable inputs.
16. No untyped process transfer: every process channel has exact Hoare-style
    send/receive contracts for state, occurrence identities, ownership, and
    obligations. The send postcondition and receive precondition meet at a
    stable in-flight escrow assertion. Every occurrence has at most one receive
    or disposition; unrestricted pending may retain it forever, while eventual
    resolution needs named progress assumptions. Physical communication must
    refine those laws.
17. One scalable algebra: serial authoring may synthesize a degenerate process
    realization, but it may not introduce an alternate semantics or theorem
    route. Explicit concurrent plans, flattened subsystems, and synthesized
    serial plans share one execution, safety, liveness, and obligation model.
18. No schedule leakage: portable process-model transitions request abstract demands;
    occurrence identity, command DAGs, batching, routing, worker assignment, and
    cancellation mechanism remain replaceable realization facts unless the
    product explicitly observes them.
19. Byte flow before framing: partial reads and writes refine one asynchronous
    ordered-byte protocol. No parser, codec, or application may assume provider
    call boundaries are message boundaries, and an egress retry may address only
    the uniquely retained suffix.
20. Quantitative compositionality: process and subgraph certificates expose
    resource theorems. Affine transfers are not double-counted, shared storage is
    charged according to an explicit metric law, dynamic population is bounded,
    and finite channel capacity is enforced by transferable credit and a real
    backpressure frontier.
21. No unused authored source: source elaboration, ghost erasure, raw instruction
    encoding, artifact representation, writing, loading, and decoding form one
    exact dependent identity chain. Extensional contract equivalence cannot
    replace an assembly author's selected instructions with another program.
22. No live-set freshness: process generations, channel epochs, child/message
    occurrences, and replacements are fresh over a monotone execution history;
    stale completions never regain authority after numeric reuse.
23. No unbanked standard algorithm proof: when a reusable implementation model
    is selected, exact authored/generated source proves refinement to that model
    before its once-proved specification theorem is composed. Direct extensional
    proofs remain a deliberate first-class alternative, not an accidental default.
24. No assembly-only product proof: the portable model or process composition
    proves the demanded product specification independently of platform and ISA;
    authored assembly then proves refinement to that already-verified boundary.
    Moving operational definitions out of a precious `Spec` module is encouraged
    when it improves minimality, but it must not erase the platform-independent
    satisfaction theorem or force each realization to re-prove product logic.

## 5. Change policy

Top-level theorem statements and trust boundaries receive the highest review
care because Lean cannot prove that they express the intended real-world claim.
Implementations beneath them are replaceable. When a requirement changes, the
preferred workflow is a branch, deletion of obsolete machinery, and a clean
rebuild against the reviewed interface. Git preserves old implementations.

Formal review therefore evaluates theorem adequacy as well as kernel acceptance.
For material theorem families, the reviewer distinguishes universal proofs from
point fixtures, checks non-vacuity and connection to their consumers, records
why the proved statement is sufficient and where it is deliberately weaker,
and assesses proof economy by reusable abstraction rather than raw line count.
[AGENT_REVIEW.md](AGENT_REVIEW.md) owns the operational review standard.

A clean rebuild checks reproducibility after obsolete machinery is deleted; it
is not the expected incremental invalidation cone. During ordinary development,
the mandatory invalidation plan and build-execution report must show local
semantic invalidation and distinguish semantic status from elaboration, kernel
checking, generation, linking, and serialization work.

Proof-to-assembly ratios are design smells, not machine gates. Straight-line
code should normally need little local proof because libraries own reusable
refinement theorems; novel hot code may justifiably carry much more proof.
