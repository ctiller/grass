/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Grass.Std.Zlib.Gzip.Member
import Grass.Std.Zlib.Gzip.SizeBound
import Grass.Std.Zlib.Fixed32K.Checksum

/-!
# Fixed32K: the reusable fixed-Huffman/32K-window gzip codec model

`Spikes/3_Gzip/Assembly.lean` imports this module and names `Std.Zlib.Fixed32K.*`
for the algorithm it selects (`codecPlan := .fixed32KHashChain (maxProbes := 64)`).
This file is the pure-Lean codec *mathematics* half of that plan: the ported
DEFLATE fixed-Huffman encoder/decoder and RFC 1952 gzip member framing, and
their round-trip, size, and checksum theorems. It is the model
`Std.Zlib.Fixed32K.model`/`.correct` would state a contract against -- see
"Left out" below for why this file does not itself build that contract layer.

## Provenance

Ported from gasm (`C:\Users\craig\gasm\Stdlib\Zlib\`), whose zlib/DEFLATE/gzip
library is already proved end-to-end; per the owner's instruction, this port
reuses gasm's round-trip mathematics rather than re-deriving it:

* `Grass/Std/Zlib/Support.lean` -- gasm's `ByteArrayBridge.lean` (unchanged):
  generic `_root_.ByteArray.get!`/`push` lemmas the fixed-block proofs need.
* `Grass/Std/Zlib/Deflate/Huffman.lean` -- gasm's `Zlib/Huffman.lean`
  (unchanged): canonical Huffman table construction and its branch-rooted
  decode-tree invariant.
* `Grass/Std/Zlib/Deflate/Core.lean` -- gasm's `Zlib/Deflate.lean`, trimmed to
  the fixed-Huffman path: `BitReader`/`BitWriter`, `decompress` (handles all
  three RFC 1951 block kinds, since decoding a transmitted dynamic table needs
  no package-merge machinery), LZ77 (`tokenize`/`findLongestMatch`), and
  `compressFixed`. Omits `compress`/`compressPlan`/`emitDynamicBlock` and the
  package-merge optimal code-length search (`PMNode`, `packageMergeLengths`,
  `buildDynPlan`, ...) -- gasm's *dynamic*-Huffman encoder selection, which
  `codecPlan`'s always-fixed-block choice never calls.
* `Grass/Std/Zlib/Deflate/Equivalence.lean` -- gasm's `Zlib/Equivalence.lean`,
  trimmed to drop only `compress_fixed_branch` (the one theorem in that file
  about the dynamic-selecting `compress`, unreachable without the omitted
  encoder). Everything else, including `emitFixedBlock_roundtrip_soundness`,
  is unchanged.
* `Grass/Std/Zlib/Deflate/FixedBlockBridge.lean` -- gasm's
  `Zlib/FixedBlockBridge.lean` (unchanged): identifies `compressFixed` (the
  encoder `Gzip.write` below and the assembly's `process_block` implement)
  with `flushBitWriter (emitFixedBlock (tokenize ·))` (every roundtrip theorem
  in `Equivalence.lean` is stated about the latter), giving
  `compressFixed_roundtrip_soundness`.
* `Grass/Std/Zlib/Deflate/SizeBound.lean` -- gasm's `Zlib/CompressSizeBound.lean`,
  trimmed to the fixed-block bit-count bound `emitFixedBlock_length` (drops the
  dynamic-block bound and everything upstream of only it).
* `Grass/Std/Zlib/Deflate/FixedSizeBound.lean` -- new: composes the two files
  above into `compressFixed_size_bound`, the byte-level bound gasm states only
  for `compress`/`zlibCompress`, never for `compressFixed` alone.
* `Grass/Std/Zlib/Gzip/Header.lean` -- new: the fixed ten-byte RFC 1952 header
  `Assembly.lean`'s `entry` block writes, with a `Trailer.lean`-style read/write
  round trip. gasm's `Zlib/Gzip.lean` inlines the same ten bytes without naming
  or separately proving them.
* `Grass/Std/Zlib/Gzip/Member.lean` -- new: `Gzip.Member`/`Gzip.write`/
  `Gzip.inflate`/`Gzip.IsExactlyOneMember` and `write_inflate`, composing
  `Header`, the pre-existing `Grass/Std/Zlib/Gzip/Trailer.lean`, and
  `compressFixed_roundtrip_soundness` by byte-length slicing -- exactly gasm's
  own `gzipDecompress`'s `bytes.extract pos (bytes.size - 8)` strategy in
  `Zlib/ContainerRoundtrip.lean`, not a new parsing argument.
* `Grass/Std/Zlib/Gzip/SizeBound.lean` -- new: wraps `compressFixed_size_bound`
  with the header/trailer's fixed 18-byte overhead.
* CRC-32 (`Grass/Std/Zlib/CRC32.lean`) and the trailer
  (`Grass/Std/Zlib/Gzip/Trailer.lean`) are reused unchanged: both already
  existed in Grass, stated over `Grass.Std.Logical.ByteArray`/`Vec`/`BitVec`
  the way `Fixed32K/Checksum.lean`'s incremental accounting needs, and gasm's
  own table-driven CRC-32 was not ported since nothing here needs it --
  `Gzip.write` computes the trailer with `CRC32.checksum` directly, so no
  bridge between the two formulations was needed either.

## Left out (need machinery outside this library)

Per instructions, these `Spikes/3_Gzip/Assembly.lean` identifiers are not
defined here; each needs the `ComponentContract`/`ImplementationModel`/
assembly-representation framework (`Grass.Assembly`/`Grass.Specification`
machinery for binding a proved model to instruction-level code), which is a
different layer from the codec mathematics this file ports:

* `GzipImplementationPlan` and `.fixed32KHashChain` -- the plan type
  `Assembly.lean`'s `codecPlan` inhabits.
* `Std.Zlib.Fixed32K.contract` `: ComponentContract`, `.model` `:
  ImplementationModel`, `.correct` `: ImplementationRealizesContract _ _` --
  the contract/model pair `Assembly.lean` states `fixed32KModelCorrect`
  against.
* `Std.Zlib.Fixed32K.staticObjects`, `.outputSinkContract` -- the `asm_source`
  literal-data and abstract-output-sink pieces `Assembly.lean`'s `gzipSource`
  and `codecAlgorithmScope` need.
* `Std.Zlib.Fixed32K.arenaRepresentation` -- the `RepresentationPlan` mapping
  `Assembly.lean`'s `GzipArena` register/offset layout onto this file's
  `Deflate`/`Gzip` state, consumed by `verify_asm_scope`.

Also left out, for a narrower reason:

* `Gzip.memberFormat : Format Member` -- `Spikes/3_Gzip/Spec.lean` names it,
  but `Grass.Grammar.Format`/`Derives` (`Grass/Grammar/Core.lean`) is a
  combinator grammar over `pure`/`byte`/`seq`/`choice`/`repeat`/`refine`/`lift`/
  `iso`; expressing a Huffman/LZ77-coded bitstream in it -- and reproving
  `Derives`-level round-trip semantics for it -- would re-derive the DEFLATE
  bitstream proof a second way inside the grammar DSL, exactly the duplicated
  complicated round-trip proof this port is instructed to avoid. `Gzip.write`/
  `Gzip.inflate` below are the executable reader/writer pair instead, with
  `write_inflate` as their round trip.
* `Fixed32K.State` and the streaming construction-prefix theorem
  `fixed32k_prefix` (`docs/SPIKE_3.md` block-06) -- these describe the partial-
  input invariant during streaming (mid-`process_block`, mid-flush) arena
  state, which is part of the same implementation-model layer as
  `Std.Zlib.Fixed32K.model` above, not the whole-input codec mathematics this
  file carries. `Gzip.write`/`inflate` here are total functions on complete
  input.
-/

namespace Grass.Std.Zlib.Fixed32K

open Grass.Std.Logical

/-- The whole-input codec this plan selects: one RFC 1952 gzip member, its
payload DEFLATE-compressed as a single final fixed-Huffman block. -/
def write (input : Logical.ByteArray) : Logical.ByteArray :=
  Gzip.write ⟨input⟩

/-- **The round trip `Spikes/3_Gzip/Spec.lean`'s `successfulTraceIffOneMemberRoundTrip`
states on the right of its `↔`**: `write`'s output is exactly one gzip member,
and inflating it recovers the exact input. -/
theorem write_round_trip (input : Logical.ByteArray) :
    Gzip.IsExactlyOneMember (write input) ∧ Gzip.inflate (write input) = .ok input :=
  ⟨Gzip.isExactlyOneMember_write ⟨input⟩, Gzip.write_inflate ⟨input⟩⟩

/-- Output-size bound for the whole codec, combining
`Deflate.compressFixed_size_bound` with the container's fixed 18-byte
overhead. -/
theorem write_size_bound (input : Logical.ByteArray) :
    (write input).length ≤ 5 * input.length + 21 :=
  Gzip.write_size_bound ⟨input⟩

end Grass.Std.Zlib.Fixed32K
