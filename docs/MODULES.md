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
  Assembly/
    X86.lean     narrow first-class x86 assembly authoring facade
  Op/            existential ghost/raw operation interfaces and erasure
  ISA/
    X86.lean     narrow x86 machine-authority facade
    X86/         common, Intel, AMD, encoding, decoding, validation metadata
  ABI/
    Win64/
  Platform/
    Win32.lean   narrow Win32 API authoring facade
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
  Emit.lean      verified-program emission facade
  Programs/
    HelloWin64/
    SortWin64/
    GzipWin64/
    Http2Win64/
    CubeWin64Vulkan/
Tests/
tools/           validation and audit binaries, and the agent bus
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

The files marked as facades are stable public authoring surfaces, not a second
implementation hierarchy and not ownership of every module beneath a similarly
named directory. Their purpose is to let an assembly author name the artifact
being authored instead of manually reproducing the internal dependency graph.

`Grass.Assembly.X86` is the first-class x86 assembly authoring facade. It may
re-export the narrow instruction signatures from `Grass.ISA.X86` together with
the architecture-independent `Construct` and `CFG` signatures needed by source
forms such as `asm_source`, `withStack`, block annotations, and calls. It does
not make the x86 machine-authority owner responsible for the construction
language: the construction/lowering workstream owns this facade and consumes
the ISA facade as a dependency. An implementation or certificate module may
not enter its dependency cone merely for convenience.

`Grass.ISA.X86` is the lower machine-authority facade over the x86 encoding,
decoding, instruction semantics, and validation-metadata shards. Machine-model
authors and the assembly facade consume it directly; ordinary assembly authors
should not have to assemble its shards one by one.

`Grass.Platform.Win32` is the public facade for the Win32 API family. A Windows
version floor such as Windows 10 and an architecture/ABI selection such as x64
remain explicit profile values selected through this API; neither belongs in
the module path. In particular, the spike spelling `Grass.Platform.Win10.X64`
must be replaced by `Grass.Platform.Win32`, not retained as an alias that
conflates an API family, deployment floor, architecture, and ABI. The spike-side
replacement, including the Vulkan profile spelling, is tracked by agent-bus
dependency `g-design:86` rather than claimed complete here.

`Grass.Emit` is the safe verified-emission facade. It exposes `VerifiedProgram`
and the checked `emitProgram` entry point, plus only the result vocabulary
needed to use them. Ghost erasure, raw instruction admission, unchecked
construction, linking mechanics, and byte writers remain in their owning
`Unsafe` and `Artifact` shards. Calling the internal layer `Grass.Unsafe` does
not make it an acceptable replacement for the verified author surface, and
`Grass.Emit` must not expose a route from an unverified source directly to
executable bytes.

All four facades are signature-only and have measured dependency cones. They
may import reviewed logical or signature leaves, but never `Impl`, `Cert`, a
whole-program aggregate, or a concrete program. Facade tests demonstrate both
halves of the boundary: the intended spike vocabulary resolves through the
concise import, and representative implementation-only declarations do not.
Decision 134 ratifies `Grass.Assembly.*`, `Grass.Platform.*`, and `Grass.Emit`
as stable author-facing facades. `Grass.ISA.X86` is deliberately outside that
list: it is the narrower machine-authority integration surface consumed by
machine-model authors and `Grass.Assembly.X86`, and uses
[OLEAN_SHARDING.md](OLEAN_SHARDING.md)'s reviewed deliberate-public-re-export
exception on that basis. Neither case is permission to use `import all`.

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

Large instruction/API families are sharded mechanically without creating a
closed master sum type or duplicating semantic facts. Generated reference or
test data is versioned separately when size would burden ordinary clones/builds.

The same rule applies to process roles, protocol keys, cancellation points, and
composition witnesses. Large realizations publish module-local signatures and
opaque facet certificates; they do not construct one whole-program process sum
or a proof indexed by the complete plan. The normative design is
[PROCESS_SHARDING.md](PROCESS_SHARDING.md).

The baseline toolchain is Lean 4.33.1 with mathlib and other reviewed Lean
dependencies allowed. Dependency additions enter the appropriate TCB/build
ledger.
