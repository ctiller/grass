import Grass.Grammar.Endian

/-! # Sized endian conversion fixtures -/

namespace Grass.Tests.Grammar.Endian

open Grass.Grammar Grass.Std.Logical

def pair : SizedByteArray 2 := ⟨Vec.fromList [0x12, 0x34], by decide⟩

example : bigEndianToBitVec pair = (0x1234 : BitVec 16) := by decide

example : (@bitVecToBigEndian 2 (0x1234 : BitVec 16)).1 = pair.1 := by decide

example : (bigEndianIsomorphism 2).backward ((bigEndianIsomorphism 2).forward pair) = pair := by
  exact (bigEndianIsomorphism 2).backward_forward pair

example : (bigEndianIsomorphism 2).forward
    ((bigEndianIsomorphism 2).backward (0x1234 : BitVec 16)) = 0x1234 := by
  exact (bigEndianIsomorphism 2).forward_backward 0x1234

example : littleEndianToBitVec pair = (0x3412 : BitVec 16) := by decide

example : (@bitVecToLittleEndian 2 (0x3412 : BitVec 16)).1 = pair.1 := by decide

example : (littleEndianIsomorphism 2).backward
    ((littleEndianIsomorphism 2).forward pair) = pair := by
  exact (littleEndianIsomorphism 2).backward_forward pair

example : (littleEndianIsomorphism 2).forward
    ((littleEndianIsomorphism 2).backward (0x3412 : BitVec 16)) = 0x3412 := by
  exact (littleEndianIsomorphism 2).forward_backward 0x3412

example : bigEndianU16Format = bigEndianFormat 2 := rfl
example : bigEndianU32Format = bigEndianFormat 4 := rfl
example : bigEndianU64Format = bigEndianFormat 8 := rfl
example : littleEndianU16Format = littleEndianFormat 2 := rfl
example : littleEndianU32Format = littleEndianFormat 4 := rfl
example : littleEndianU64Format = littleEndianFormat 8 := rfl

end Grass.Tests.Grammar.Endian
