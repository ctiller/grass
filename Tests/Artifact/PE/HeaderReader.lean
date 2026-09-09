import Grass.Artifact.PE.HeaderReader

namespace Grass.Tests.Artifact.PE.HeaderReader

open Grass.Std.Logical Grass.Grammar Grass.Artifact.PE

private def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa, 0xbb]

example : takeHeaderPrefix (writeHeaderPrefix 3 ++ suffix) = .done 3 suffix := by
  simp

example : takeHeaderPrefix (Vec.replicate 80 0) = .needMore (some 8) := by
  rfl

private def badMagic : Std.Logical.ByteArray :=
  Vec.fromList [0] ++ (writeHeaderPrefix 1).drop 1

example : takeHeaderPrefix badMagic =
    .invalid (.malformed "noncanonical PE header prefix") := by
  rfl

end Grass.Tests.Artifact.PE.HeaderReader
