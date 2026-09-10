import Grass.Std.Zlib.Fixed32K.Checksum

/-! # Gzip checksum-state and trailer consumer checks -/

namespace Grass.Tests.Std.Zlib

open Grass.Std Grass.Std.Logical Grass.Std.Zlib Grass.Grammar

def digits : Logical.ByteArray := Vec.fromList [0x31, 0x32, 0x33, 0x34, 0x35,
  0x36, 0x37, 0x38, 0x39]

set_option maxRecDepth 20000 in
example : Gzip.Trailer.write (Fixed32K.ChecksumState.initial.account digits).trailer =
    Vec.fromList [0x26, 0x39, 0xf4, 0xcb, 9, 0, 0, 0] := by decide

example (trailer : Gzip.Trailer) (suffix : Logical.ByteArray) :
    Gzip.Trailer.read (trailer.write ++ suffix) = .done trailer suffix :=
  Gzip.Trailer.read_write_append trailer suffix

example (input : Logical.ByteArray) (short : input.length < 8) :
    Gzip.Trailer.read input = .needMore (some (8 - input.length)) :=
  Gzip.Trailer.read_short short

example : Gzip.Trailer.read (Vec.fromList [0, 0, 0, 0, 0, 0, 0]) =
    .needMore (some 1) := rfl

example (left right suffix : Logical.ByteArray) :
    Gzip.Trailer.read
      ((Fixed32K.ChecksumState.initial.account left |>.account right).trailer.write ++ suffix) =
        .done ⟨CRC32.checksum (left ++ right), BitVec.ofNat 32 (left ++ right).length⟩ suffix := by
  apply Fixed32K.ChecksumState.read_written_trailer
  apply Fixed32K.ChecksumState.account_represents
  simpa using Fixed32K.ChecksumState.account_represents
    Fixed32K.ChecksumState.initial_represents left

example : Gzip.Trailer.write Fixed32K.ChecksumState.initial.trailer =
    Vec.replicate 8 0 := by decide

end Grass.Tests.Std.Zlib
