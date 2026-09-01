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
  Process/
    Protocol/    nominal registries, demands/results, optional view facets
    Network/     populations, lifecycle, Hoare channels, escrow, supervision
    Proof/       adequacy, simulation, global-loop lifting, physical templates
    ByteFlow/    partial async I/O, lifecycle, framing-independent byte streams
    Resource/    owned metrics, capacity credit, scope bounds and flux
    Flatten/     fractal hiding, sequential adapter, complete serial schedulers
    Trace/       independence diamonds, partial orders, syscall commutation
    Function/    direct terminating serial-call and exported callable bridges
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
  Build/
    Cache/       semantic-environment Merkle keys and certificate replay
    Manifest/    measured shards and hierarchical composition certificates
  Unsafe/        raw construction, import, stepping, and emission
  Programs/
    HelloWin64/
    SortWin64/
    GzipWin64/
    Http2Win64/
    CubeWin64Vulkan/
Tests/
Tools/
docs/
references/
```

Before those libraries exist, `Spikes/` contains the comment-free expected
author modules which pressure-test the interfaces without pretending to compile:

```text
Spikes/
  1_Hello_World/     Resource Spec Projection Process Plan Assembly Program Artifact
  2_Sort/            Resource Spec Projection Process Model Plan Data Macros Assembly Bindings Program Artifact
  3_Gzip/            Resource Spec Projection Process Model Plan Data Assembly Bindings Program Artifact
  4_Web_Server/      Resource Spec Projection Model Process Cancellation Plan Data Macros Assembly SourceClosure Bindings Program Artifact
  5_Spinning_Cube/   Resource Spec Projection Process Staged Model Plan Assembly SourceClosure Program Artifact
```

These are design fixtures, not an alternate library tree. When implementation
begins, reusable declarations move to the owned `Grass/` modules and spike files
remain small clients or golden author-surface tests. Explanatory proof comments
remain in `docs/SPIKE_n.md`; the matching `.lean` files show only the source and
proof terms an author is expected to maintain.

The displayed file split maximizes adversarial inspectability during design; it
is not mandatory product ceremony. Public syntax may place several logical
sections in one source file and generate closure, expansion, parser/writer, and
artifact packaging witnesses. Conversely, large programs may shard a logical
section. Physical module boundaries are chosen from measured elaboration,
kernel-check, cache, and filesystem costs while the dependency tiers above stay
intact; Grass mandates neither one module per basic block nor three files per
program.

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
