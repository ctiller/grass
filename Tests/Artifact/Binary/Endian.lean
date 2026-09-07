import Grass.Artifact.Binary.Endian

/-! # Concrete endian reader and writer fixtures -/

namespace Grass.Tests.Artifact.Binary.Endian

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa]

example : takeBigEndian 2 (Vec.fromList [0x12, 0x34, 0xaa]) =
    .done (0x1234 : BitVec 16) suffix := by rfl

example : writeBigEndian (count := 2) (0x1234 : BitVec 16) =
    Vec.fromList [0x12, 0x34] := by decide

example : takeLittleEndian 2 (Vec.fromList [0x12, 0x34, 0xaa]) =
    .done (0x3412 : BitVec 16) suffix := by rfl

example : writeLittleEndian (count := 2) (0x3412 : BitVec 16) =
    Vec.fromList [0x12, 0x34] := by decide

example : takeBigEndian 2 (writeBigEndian (count := 2) (0x1234 : BitVec 16)) =
    .done 0x1234 Vec.empty := by
  exact takeBigEndian_writeBigEndian 0x1234

example : takeLittleEndian 2 (writeLittleEndian (count := 2) (0x3412 : BitVec 16)) =
    .done 0x3412 Vec.empty := by
  exact takeLittleEndian_writeLittleEndian 0x3412

end Grass.Tests.Artifact.Binary.Endian
