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

import Grass.Std.Logical.HostBytes
import Grass.Std.Zlib.CRC32
import Grass.Std.Zlib.Gzip.Header
import Grass.Std.Zlib.Gzip.Trailer
import Grass.Std.Zlib.Deflate.FixedBlockBridge

/-!
# Gzip member framing (RFC 1952), fixed-Huffman only

This is `Spikes/3_Gzip`'s codec surface: a single RFC 1952 member whose payload
is always DEFLATE-encoded as one final fixed-Huffman (BTYPE=01) block. It wraps
the ported `Grass.Std.Zlib.Deflate.compressFixed`/`decompress`
(`Grass/Std/Zlib/Deflate/Core.lean`, `.../Equivalence.lean`,
`.../FixedBlockBridge.lean` -- gasm's `Stdlib/Zlib/Deflate.lean`,
`Equivalence.lean`, `FixedBlockBridge.lean`, ported unchanged) in the fixed
ten-byte `Header` and the existing `Trailer` (CRC-32 then ISIZE, both
little-endian), exactly as `Spikes/3_Gzip/Assembly.lean`'s authored `entry`/
`input_eof` blocks build a member: header, then one `process_block` call per
32KiB input chunk, then the CRC/ISIZE trailer.

The member/trailer split does not run a boundary-sensing parse over the
compressed bytes -- gasm's own `Stdlib/Zlib/ContainerRoundtrip.lean` doesn't
either. Both slice by *length*: the compressed payload is whatever sits between
the fixed ten-byte header and the fixed eight-byte trailer, exactly gasm's
`gzipDecompress`'s `bytes.extract pos (bytes.size - 8)`. This sidesteps ever
needing "decoding a complete block ignores trailing bytes" as a fact about
`decompress` -- a fact gasm does not state either, and this module does not
add.

`Gzip.Member` deliberately carries only the payload. RFC 1952's other fields
(MTIME, XFL, OS, and the optional FEXTRA/FNAME/FCOMMENT/FHCRC blocks) are
constant for every member this codec ever writes (`header`'s docstring), so a
`GzipMetadata` field of the kind `docs/SPIKE_3.md` block-05 sketches would
carry no information here; adding it is future work for a codec that varies
those bytes, not a gap in this one.
-/

namespace Grass.Std.Zlib.Gzip

open Grass.Std.Logical Grass.Grammar Grass.Std.Zlib

/-- One gzip member as this codec produces and consumes it: an RFC 1952
container around a single fixed-Huffman DEFLATE payload. -/
structure Member where
  payload : Logical.ByteArray
deriving DecidableEq, Repr

/-- Serialize a member: fixed header, `compressFixed`'s output crossed to the
logical `ByteArray`, then the CRC-32/ISIZE trailer computed from the payload
exactly as `Fixed32K/Checksum.lean`'s `ChecksumState.trailer` computes it from
the accounted prefix. -/
def write (m : Member) : Logical.ByteArray :=
  header ++
    Vec.ofHostBytes (Deflate.compressFixed (Vec.toHostBytes m.payload)) ++
    Trailer.write ⟨CRC32.checksum m.payload, BitVec.ofNat 32 m.payload.length⟩

/-- Deserialize a member: strip the fixed header, split the remainder by
length into "everything but the last eight bytes" (the compressed payload)
and "the last eight bytes" (the trailer), invert `compressFixed` with the
ported `decompress`, and accept only if the trailer's CRC-32 and ISIZE match
the recovered payload. Any other case is a classified failure string; the
precious fact is `write_inflate` below, not this function's diagnostics. -/
def inflate (bytes : Logical.ByteArray) : Except String Logical.ByteArray :=
  match readHeader bytes with
  | .done () rest =>
    if rest.length < 8 then
      .error "gzip stream too short for trailer"
    else
      let compressedLen := rest.length - 8
      match Trailer.read (rest.drop compressedLen) with
      | .done trailer _ =>
        match Deflate.decompress (Vec.toHostBytes (rest.take compressedLen)) with
        | .ok hostPayload =>
          let payload := Vec.ofHostBytes hostPayload
          if trailer.crc32 = CRC32.checksum payload ∧
              trailer.inputSize = BitVec.ofNat 32 payload.length then
            .ok payload
          else
            .error "gzip CRC32/ISIZE mismatch"
        | .error _ => .error "gzip DEFLATE stream malformed"
      | _ => .error "gzip trailer malformed"
  | _ => .error "gzip header malformed"

/-- These bytes are, in their entirety, one well-formed gzip member: the
existential form `Spikes/3_Gzip/Spec.lean`'s `Gzip.IsExactlyOneMember` needs,
matching `Console.streamingGzipContract_success_iff`'s "exactly one member"
reading (no leftover bytes, no second member). -/
def IsExactlyOneMember (bytes : Logical.ByteArray) : Prop :=
  ∃ m : Member, bytes = write m

/-- **Gzip member round trip.** `inflate` inverts `write` on every payload.
The compressed-payload length arithmetic here is new (gasm slices its own
`gzipCompress`/`gzipDecompress` the same way but never states it for
`compressFixed`+`Header`+`Trailer` separately); the DEFLATE inversion inside
it is `Deflate.compressFixed_roundtrip_soundness`
(`Grass/Std/Zlib/Deflate/FixedBlockBridge.lean`), ported from gasm unchanged. -/
theorem write_inflate (m : Member) : inflate (write m) = .ok m.payload := by
  have hcomp : (Deflate.compressFixed (Vec.toHostBytes m.payload)).size + 8 =
      (Vec.ofHostBytes (Deflate.compressFixed (Vec.toHostBytes m.payload)) ++
        Trailer.write ⟨CRC32.checksum m.payload, BitVec.ofNat 32 m.payload.length⟩).length := by
    simp [Trailer.length_write]
  unfold write inflate
  rw [Vec.append_assoc, readHeader_append]
  simp only
  rw [if_neg (by omega : ¬
    (Vec.ofHostBytes (Deflate.compressFixed (Vec.toHostBytes m.payload)) ++
      Trailer.write ⟨CRC32.checksum m.payload, BitVec.ofNat 32 m.payload.length⟩).length < 8)]
  rw [show (Vec.ofHostBytes (Deflate.compressFixed (Vec.toHostBytes m.payload)) ++
      Trailer.write ⟨CRC32.checksum m.payload, BitVec.ofNat 32 m.payload.length⟩).length - 8 =
      (Vec.ofHostBytes (Deflate.compressFixed (Vec.toHostBytes m.payload))).length from by
    simp [Trailer.length_write]]
  simp only [Vec.drop_append_of_length_eq rfl, Vec.take_append_of_length_eq rfl,
    Trailer.read_write, Vec.toHostBytes_ofHostBytes,
    Deflate.compressFixed_roundtrip_soundness, Vec.ofHostBytes_toHostBytes,
    and_self, if_true]

/-- Every member `write` produces satisfies `IsExactlyOneMember`. -/
theorem isExactlyOneMember_write (m : Member) : IsExactlyOneMember (write m) := ⟨m, rfl⟩

end Grass.Std.Zlib.Gzip
