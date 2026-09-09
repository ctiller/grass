import Grass.ISA.X86.Bytes
import Grass.Artifact.Binary.Endian

/-! Connection between x86's 32-bit byte helper and the shared endian writer. -/
namespace Grass.ISA.X86

open Grass.Std.Logical

/-- The x86 four-byte helper is exactly the grammar's canonical little-endian
representation, after converting its list result to the shared byte vector. -/
theorem le32_toLittleEndian (value : BitVec 32) :
    Vec.fromList (le32 value) =
      (@Grass.Grammar.bitVecToLittleEndian 4 value).1 := by
  apply Vec.toList_injective
  simp [le32, Grass.Grammar.bitVecToLittleEndian, Grass.Grammar.reverseSized,
    Grass.Grammar.bitVecToBigEndian, Grass.Grammar.unpackBigList]

/-- The x86 four-byte helper agrees byte-for-byte with the artifact binary
writer used by PE serialization. -/
theorem le32_writeLittleEndian (value : BitVec 32) :
    Vec.fromList (le32 value) =
      Grass.Artifact.Binary.writeLittleEndian (count := 4) value := by
  exact le32_toLittleEndian value

end Grass.ISA.X86
