# Initial repository and module structure

The structure follows semantic ownership and permits parallel, cached builds.
Names are provisional; dependency direction is normative.

```text
Grass/
  Core/          identifiers, values, result and utility laws
  Std/
    Logical/     pure Vec/ByteArray, lists, maps, iterators and algebraic laws
    Owned/       OwnedVec, physical slices, allocation and cleanup realizations
  Specification/ neutral boundaries, demands/results, requirement keys and typed junctions
  Semantics/     precious SpecProcess behavior, traces, observations, oracle, progress
  Grammar/       typed text/binary formats, derivations, streaming parser and writer laws
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
  Refinement/    presentations and proofs connecting semantics to replaceable realizations
  Weave/         composition and noninteraction
  CFG/           block contracts, edges, loops, calls, stack shapes
  Construct/     layouts, placement, verified instruction-fragment generators
  Op/            existential ghost/raw operation interfaces and erasure
  ISA/
    X86/         common, Intel, AMD, encoding, decoding, validation metadata
  ABI/
    Win64/
  Platform/
    Win32/
  Artifact/
    Binary/      concrete readers/writers realizing Grammar formats
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
  1_Hello_World/     Spec Program
  2_Sort/            Spec Assembly Program
  3_Gzip/            Spec Assembly Program
  4_Web_Server/      Spec Process Cancellation Macros Assembly Program
  5_Spinning_Cube/   Spec Process Macros Assembly Layout Program
```

These are design fixtures, not an alternate library tree. When implementation
begins, reusable declarations move to the owned `Grass/` modules and spike files
remain small clients or golden author-surface tests. Explanatory proof comments
remain in `docs/SPIKE_n.md`; the matching `.lean` files show only the source and
proof terms an author is expected to maintain.

The displayed files are the expected author-maintained surface and therefore
count as ceremony. Generated closure, expansion, parser/writer, cancellation
maps, and artifact packaging remain inspectable in the annotated documents and
tool reports but do not receive authored files. Conversely, large programs may
shard a genuinely independent logical or machine subsystem. Physical module
boundaries are chosen from authored abstraction and measured build locality,
not from the number of internal certificate-record fields. See
[SPIKE_AUTHORING.md](SPIKE_AUTHORING.md). The required public/private module
split, opaque certificate boundary, Lake facets, aggregate DAG, and rebuild-cone
ratchet are specified in [OLEAN_SHARDING.md](OLEAN_SHARDING.md).

Lower layers must not import concrete programs. Common semantics must not import
one ISA or platform. ISA and platform profiles may depend on common memory/event
vocabulary but own their consistency and applicability rules. Artifact writers
consume raw layout/link descriptions, not high-level specifications.

The foundational dependency graph is an acyclic diamond rather than a single
chain:

```text
Core
  -> Std.Logical
      -> Specification
          -> Semantics
          -> Process
      -> Memory / Obligation
          -> Std.Owned

Semantics + Process
  -> Refinement / Weave
  -> higher consumers
```

`Std.Logical` owns pure collection facts and imports no memory/obligation layer.
Memory and obligations may consume its finite sequences/maps. `Std.Owned`
specializes the already-owned memory and obligation models into physical
containers; Memory and Obligation must never import it. Artifact, CFG, decoder,
trace, and program modules consume the lowest suitable layer and must not
introduce competing byte-array or ordered-buffer foundations.

`Specification` is neutral vocabulary, not precious program behavior and not a
process realization. It imports neither `Semantics` nor `Process`.
`Semantics` owns `SpecProcess` and `BehaviorContract`; `Process` owns replaceable
network shapes and execution machinery. Neither imports the other to state its
core objects. `Refinement` or `Weave` imports both when proving that one selected
process presentation has exactly the behavior and requirements of a
`SpecProcess`. This cut prevents a convenient boundary record from creating a
Semantics/Process import cycle and keeps the non-precious process presentation
out of precious program identity.

`ScopeId` is a general reviewed namespace path and belongs in dependency-minimal
`Core`, not in `Specification`, `Process`, or the memory identity model. It is
not a fresh execution identity: allocation, occurrence, and process-generation
identities retain their separate generative laws. `Specification` consumes
`ScopeId` when forming requirement keys; process and other registries may use it
without importing a higher subsystem merely to name their scopes.

Large instruction/API families are sharded mechanically without creating a
closed master sum type or duplicating semantic facts. Generated reference or
test data is versioned separately when size would burden ordinary clones/builds.

The concise imports shown in `Spikes/` are stable authoring facades, not a
fictional second module tree. `Grass.Spec.Console`, `Grass.Spec.Grammar`,
`Grass.Spec.Graphics`, and `Grass.Spec.Resource` re-export the corresponding
typed specification-language signatures. `Grass.Process`,
`Grass.Process.Cancellation`, and `Grass.Process.Blend` expose the stable process
authoring surface; the last may be implemented by `Refinement`/`Weave` without
changing its public import. `Grass.Assembly.X86`, `Grass.Assembly.Spirv`, the
`Grass.Platform.Win10.*` profiles, and `Grass.Emit` are likewise narrow public
facades over their owning signature modules.

A facade imports only reviewed logical or `Sig` modules needed for that public
surface. It never imports an `Impl`, `Cert`, whole-program aggregate, or concrete
program. This is the deliberate public-re-export exception anticipated by
`OLEAN_SHARDING.md`, not permission for a leaf to use `import all`. Facade
dependency cones are measured, and an implementation-only edit must not rewrite
one.

The same rule applies to process roles, protocol keys, cancellation points, and
composition witnesses. Large realizations publish module-local signatures and
opaque facet certificates; they do not construct one whole-program process sum
or a proof indexed by the complete plan. The normative design is
[PROCESS_SHARDING.md](PROCESS_SHARDING.md).

The baseline toolchain is Lean 4.33.1 with mathlib and other reviewed Lean
dependencies allowed. Dependency additions enter the appropriate TCB/build
ledger.
