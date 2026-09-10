import Grass.Std.Zlib.CRC32

namespace Grass.Tests.Std.Zlib.CRC32

open Grass.Std.Logical
open Grass.Std.Zlib.CRC32

def digits : Grass.Std.Logical.ByteArray :=
  Vec.fromList [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

set_option maxRecDepth 100000 in
example : checksum digits = 0xcbf43926 := by decide

example (poly c : BitVec 32) (left right : Grass.Std.Logical.ByteArray) :
    updateRaw poly c (left ++ right) = updateRaw poly (updateRaw poly c left) right :=
  updateRaw_append poly c left right

example (poly c : BitVec 32) (bytes : Grass.Std.Logical.ByteArray) :
    updateRaw poly c bytes = maskedUpdateRaw poly c bytes :=
  updateRaw_eq_maskedUpdateRaw poly c bytes

end Grass.Tests.Std.Zlib.CRC32
