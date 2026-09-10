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

import Grass.Grammar.Core

/-!
# Gzip member header

RFC 1952 section 2.3.1 fixes the ten-byte gzip member header: two magic bytes,
a compression-method byte, a flag byte, a four-byte modification time, an
extra-flags byte, and an operating-system byte. Every member this codec writes
carries the same ten bytes: ID1=0x1f, ID2=0x8b, CM=8 (DEFLATE), FLG=0 (no
optional fields), MTIME=0, XFL=0, OS=255 (unknown) -- matching
`Spikes/3_Gzip/Assembly.lean`'s authored `entry` block (`mov rax,
0x0000000000088b1f` for the first eight bytes, then `mov word ptr
[rdi + GzipHeader.extraFlags], 0xff00` for XFL/OS). This module has no
analogue in gasm's `Stdlib/Zlib`, whose `gzipCompress`/`gzipDecompress`
(`Stdlib/Zlib/Gzip.lean`) inline the same ten bytes without naming the
constant or proving a standalone round trip; it is sized and proved like
`Grass/Std/Zlib/Gzip/Trailer.lean`, this codec's other fixed-width framing
record. See https://www.rfc-editor.org/rfc/rfc1952.html#section-2.3.1.
-/

namespace Grass.Std.Zlib.Gzip

open Grass.Std.Logical Grass.Grammar

/-- The fixed ten-byte header this codec emits for every member. -/
def header : Logical.ByteArray :=
  Vec.fromList [(0x1f : Byte), 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff]

@[simp] theorem length_header : header.length = 10 := by
  simp [header, Vec.length]

/-- Recognize and strip the deterministic header, reporting the exact deficit
on a short prefix and a malformed-input classification on any other content
(`Format`'s `malformed` class, matching `Grass.Grammar.ParseError`). -/
def readHeader (input : Logical.ByteArray) : ParseResult Unit :=
  if input.length < 10 then .needMore (some (10 - input.length))
  else if input.take 10 = header then .done () (input.drop 10)
  else .invalid (.malformed "gzip header magic/flags/CM mismatch")

/-- `readHeader_append` retains the exact arbitrary suffix after a header,
mirroring `Trailer.read_write_append`. -/
@[simp] theorem readHeader_append (suffix : Logical.ByteArray) :
    readHeader (header ++ suffix) = .done () suffix := by
  simp [readHeader, length_header, Vec.take_append_of_length_eq length_header,
    Vec.drop_append_of_length_eq length_header]

/-- `readHeader_short` returns the exact number of bytes needed to complete a
header. -/
theorem readHeader_short {input : Logical.ByteArray} (short : input.length < 10) :
    readHeader input = .needMore (some (10 - input.length)) := by
  simp [readHeader, short]

end Grass.Std.Zlib.Gzip
