# Foundation and trust contract

## 1. Mission

Grass constructs executable programs by refining a high-level Lean
specification into a typed control-flow graph and finally raw target
instructions. It must prove that every permitted execution of the emitted
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
Specification
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

## 5. Change policy

Top-level theorem statements and trust boundaries receive the highest review
care because Lean cannot prove that they express the intended real-world claim.
Implementations beneath them are replaceable. When a requirement changes, the
preferred workflow is a branch, deletion of obsolete machinery, and a clean
rebuild against the reviewed interface. Git preserves old implementations.

Proof-to-assembly ratios are design smells, not machine gates. Straight-line
code should normally need little local proof because libraries own reusable
refinement theorems; novel hot code may justifiably carry much more proof.
