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

import Grass.Std.Zlib.Deflate.SizeBound
import Grass.Std.Zlib.Deflate.FixedBlockBridge

/-!
# Output-size bound for `compressFixed`

`Grass/Std/Zlib/Deflate/SizeBound.lean` bounds the ghost bit count of
`emitFixedBlock`, ported unchanged from gasm's `Stdlib/Zlib/CompressSizeBound.lean`.
`Grass/Std/Zlib/Deflate/FixedBlockBridge.lean`'s `compressFixed_eq_emitFixedBlock`
(gasm's Law 12 connection theorem) identifies `compressFixed` -- the encoder this
codec's `Gzip.write` actually calls -- with that ghost-bit-counted construction.
This file composes the two into the size bound `Spikes/3_Gzip`'s deliverable asks
for, stated directly about `compressFixed`. Neither ported file states this
corollary; the composition here is arithmetic, not new DEFLATE mathematics.
-/

namespace Grass.Std.Zlib.Deflate

/-- **Output-size bound for the fixed-Huffman encoder.** `compressFixed` never
expands its input by more than a factor of 5 plus a small constant: at most 36
ghost bits (`emitFixedBlock_length`) per LZ77 token, at most one token per input
byte (`tokenize_length`), one flushed padding byte, and 12 end-of-block/header
ghost bits become at most `36/8 = 4.5` bytes per input byte after flushing. -/
theorem compressFixed_size_bound (data : ByteArray) :
    (compressFixed data).size ≤ 5 * data.size + 3 := by
  rw [compressFixed_eq_emitFixedBlock]
  have hbits := flushed_size_le_bits (emitFixedBlock (tokenize data))
  have hlen := emitFixedBlock_length (tokenize data) (tokenize_rangesOk data)
  have htoklen : (tokenize data).toList.length = (tokenize data).size := by
    simp [Array.length_toList]
  have htok := tokenize_length data
  omega

end Grass.Std.Zlib.Deflate
