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

end Grass.Tests.Grammar.Endian
