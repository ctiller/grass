import Grass.ISA.X86.Bytes
import Grass.Artifact.Binary.Endian

/-! Connections between x86's 32- and 64-bit byte helpers and the shared
endian representation. -/
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

/-- The x86 eight-byte helper is exactly the grammar's canonical little-endian
representation, after converting its list result to the shared byte vector. -/
theorem le64_toLittleEndian (value : BitVec 64) :
    Vec.fromList (le64 value) =
      (@Grass.Grammar.bitVecToLittleEndian 8 value).1 := by
  apply Vec.toList_injective
  simp [le64, Grass.Grammar.bitVecToLittleEndian, Grass.Grammar.reverseSized,
    Grass.Grammar.bitVecToBigEndian, Grass.Grammar.unpackBigList]

/-- Any exact-width byte value whose underlying list is `le64 value` decodes
to that value through the grammar's canonical little-endian interpretation. -/
theorem littleEndianToBitVec_of_le64 (bytes : Grass.Grammar.SizedByteArray 8)
    (value : BitVec 64) (exactBytes : bytes.1.toList = le64 value) :
    Grass.Grammar.littleEndianToBitVec bytes = value := by
  have bytesEq : bytes = @Grass.Grammar.bitVecToLittleEndian 8 value := by
    apply Grass.Grammar.SizedVec.ext
    apply Vec.toList_injective
    rw [exactBytes]
    exact congrArg Vec.toList (le64_toLittleEndian value)
  rw [bytesEq]
  exact @Grass.Grammar.littleEndianToBitVec_bitVecToLittleEndian 8 value

end Grass.ISA.X86
