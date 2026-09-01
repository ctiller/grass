# Milestone 3: bounded-memory streaming gzip

The complete annotated proof proposal is [SPIKE_3.md](SPIKE_3.md). This file is
the concise acceptance checklist.

## Product and specification

- The precious program is a binary filter: read arbitrary bytes from stdin and
  write one interoperable RFC 1952 gzip member to stdout.
- Successful output decompresses to exactly the input. The specification does
  not make a particular compressor, block partition, compression ratio, header
  timestamp, or operating-system field precious.
- The selected artifact is deterministic: 32 KiB input blocks, fixed-Huffman
  DEFLATE, bounded greedy hash-chain LZ77, `FLG = 0`, `MTIME = 0`, `XFL = 0`,
  and `OS = 255`.
- Empty input emits a valid empty member. CRC-32 and ISIZE are exact; ISIZE is
  input length modulo 2^32 as required by the format.
- Allocation/std-handle failure before emission leaves stdout empty. A read or
  write failure after emission begins may leave only a proved prefix of the
  selected canonical member construction. All failures terminate nonzero.
- Finite input plus responsive APIs implies termination. Infinite input is a
  productive reactive execution with bounded live memory and infinitely many
  reachable input/output frontiers; safety is unconditional.

## Reusable codec surface

- `Std.Zlib.Deflate` owns bit order, fixed/dynamic/stored parsing, canonical
  Huffman decoding, LZ77 overlap semantics, and format error taxonomy.
- `Std.Zlib.Gzip` owns the RFC 1952 reader/writer, CRC-32, ISIZE, optional header
  parsing, concatenated-member behavior, and trailing-data policy.
- Every writer has a total reader. Universally quantified proofs establish
  `read (write x) = .ok x`, parser correctness, and successful-input
  canonicalization. No example execution or `native_decide` is proof authority.
- The gasm fixed-block and LZ77 round-trip results are useful spare parts, but
  their missing dynamic-Huffman/container closure is not inherited as fact.

## Process model acceptance

- [ ] The precious root `SpecProcess` contains only the captured gzip language,
  byte relation,
  outcomes, bounded-memory demand, and conditional progress. It names no block
  size, compressor stage, API order, allocator, or operating system.
- [ ] The unique standard serial gzip relation is selected from the
  specification. `SequentialAdapter` synthesizes one root plus occurrence-
  indexed console, arena, and terminal API children with complete lifecycle/
  result semantics; neither witness is application-maintained.
- [ ] The generated plan and `gzipProcessPlanRealizes` proof are inspectable but
  not application-maintained; they establish non-vacuity, exact escrows,
  child-choice completeness, coupled executions, and global progress.
- [ ] `Std.Zlib` may itself be proved as CRC/LZ/Huffman/bit-writer subprocesses,
  then flattened and serialized to the one stateful transducer used here.
  Buffering, pass fusion, and scheduling are replaceable; decoded output,
  failure-prefix behavior, bounded live memory, and productivity are semantic.
- [ ] `VerifiedProgram spec` remains indexed only by `spec`; it consumes the
  process realization and complete `AsmSource` without making the weave
  precious.

## Realization

- Win32 x64, Windows 10 API baseline, common Intel/AMD x86-64, PE32+ with ASLR.
- Exact APIs: `GetProcessHeap`, `HeapAlloc`, `GetStdHandle`, `ReadFile`,
  `WriteFile`, and `ExitProcess`; imports are derived from the realized program.
- One process-heap root is partitioned into typed state, 32 KiB input, 65,536
  `UInt16` hash heads, 32,768 `UInt16` predecessor links, and 64 KiB output.
- Dictionary generations prevent stale `UInt16` offsets from crossing block
  boundaries. Successful re-use never revives old provenance.
- All allocation occurs before stdout becomes observable. Process exit adopts
  the one process-heap cleanup obligation under the selected terminal profile.
- Fixed-Huffman, 32 KiB block, hash-chain, and `maxProbes` choices belong to the
  local `codecPlan`, not `PlatformPlan`; tuning them does not invalidate Win32,
  ABI, or loader provider proofs.

## Assembly and proof acceptance

1. `SPIKE_3.md` displays every algorithmic, API, error, cleanup, loop, and
   terminal path as literal raw instructions or as a fully displayed transparent
   macro expansion. No helper contract stands in for a missing body.
2. Local block types check register, stack, memory, initialized-range,
   obligation, pending, fault, interruption, and progress conditions at every
   call and jump.
3. Every emitted LZ77 reference proves `1 <= distance <= 32768`,
   `3 <= length <= 258`, and equality to the referenced possibly-overlapping
   source bytes. Search heuristics may affect size, never correctness.
4. Bit-writer, fixed-code, length/distance-table, block-finality, CRC-32,
   ISIZE, read fragmentation, write-all, and prefix-on-failure proofs compose to
   exact refinement of the portable specification.
5. Ghost erasure produces only the displayed raw x86-64 program. Semantic
   decoding connects the exact `.text`; PE writer/reader, imports, relocations,
   unwind, loader, and emitted-byte theorems close `VerifiedProgram.sound`.
6. The transitive axiom audit rejects `sorry`, unsafe proof authority,
   dependency-defined axioms, and `native_decide`.
7. RFC vectors, differential gzip/zlib probes, malformed streams, API response
   fuzzers, instruction/hardware checks, and native round trips challenge the
   model but never replace universal proofs.

## Deliberate non-goals of the first artifact

Dynamic-Huffman emission, user-selected levels, filenames/timestamps, multiple
input operands, decompression CLI mode, dictionaries, and parallel compression
are product extensions. The standard reader is designed not to block them. The
first executable is a real interoperable streaming compressor, but it is not
presented as feature parity with mature `gzip` tools or zlib's compression
ratio. These are disclosed product boundaries, not assumptions used to weaken
safety or round-trip correctness.
