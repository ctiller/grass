import Grass.Artifact.Binary.Unary

namespace Grass.Tests.Artifact.Binary.Unary

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

private def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa, 0xbb]

example : readUnaryNat (writeUnaryNat 3 ++ suffix) = .done 3 suffix := by
  simp

example : Derives unaryNatFormat (writeUnaryNat 3 ++ suffix) 3 suffix := by
  simpa [writeUnaryNat] using unaryNat_derives 3 suffix

example : readUnaryNat (writeUnaryNat 3 ++ suffix) = .done 3 suffix ↔
    Derives unaryNatFormat (writeUnaryNat 3 ++ suffix) 3 suffix :=
  readUnaryNat_done_iff _ _ _

example : readUnaryNat (Vec.fromList [1, 1, 1]) = .needMore (some 1) := by
  rfl

example : readUnaryNat (Vec.fromList [1, 2]) =
    .invalid (.malformed "noncanonical unary natural") := by
  rfl

end Grass.Tests.Artifact.Binary.Unary
