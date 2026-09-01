# Initial repository and module structure

The structure follows semantic ownership and permits parallel, cached builds.
Names are provisional; dependency direction is normative.

```text
Grass/
  Core/          identifiers, values, result and utility laws
  Std/
    Logical/     pure Vec/ByteArray, lists, maps, iterators and algebraic laws
    Owned/       OwnedVec, physical slices, allocation and cleanup realizations
  Semantics/     execution, traces, observations, oracle, progress
  Memory/        regions, provenance, loans, events, concurrency, arenas
  Obligation/    existential obligations, ledger, dispositions
  Effect/        abstract law-bearing monads and requirements
  Weave/         composition and noninteraction
  CFG/           block contracts, edges, loops, calls, stack shapes
  Op/            existential ghost/raw operation interfaces and erasure
  ISA/
    X86/         common, Intel, AMD, encoding, decoding, validation metadata
  ABI/
    Win64/
  Platform/
    Win32/
  Artifact/
    Binary/      byte readers/writers and general parser laws
    COFF/
    PE/
  Verify/        VerifiedProgram and composed connection theorems
  Unsafe/        raw construction, import, stepping, and emission
  Programs/
    HelloWin64/
Tests/
Tools/
docs/
references/
```

Lower layers must not import concrete programs. Common semantics must not import
one ISA or platform. ISA and platform profiles may depend on common memory/event
vocabulary but own their consistency and applicability rules. Artifact writers
consume raw layout/link descriptions, not high-level specifications.

The dependency chain is strict:

```text
Core
  -> Std.Logical
  -> Semantics / Memory / Obligation
  -> Std.Owned
  -> higher consumers
```

`Std.Logical` owns pure collection facts and imports no memory/obligation layer.
Memory and obligations may consume its finite sequences/maps. `Std.Owned`
specializes the already-owned memory and obligation models into physical
containers; Memory and Obligation must never import it. Artifact, CFG, decoder,
trace, and program modules consume the lowest suitable layer and must not
introduce competing byte-array or ordered-buffer foundations.

Large instruction/API families are sharded mechanically without creating a
closed master sum type or duplicating semantic facts. Generated reference or
test data is versioned separately when size would burden ordinary clones/builds.

The baseline toolchain is Lean 4.33.1 with mathlib and other reviewed Lean
dependencies allowed. Dependency additions enter the appropriate TCB/build
ledger.
