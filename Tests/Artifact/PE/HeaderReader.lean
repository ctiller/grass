import Grass.Artifact.PE.HeaderReader

namespace Grass.Tests.Artifact.PE.HeaderReader

open Grass.Std.Logical Grass.Grammar Grass.Artifact.PE

private def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa, 0xbb]

example : takeHeaderPrefix (writeHeaderPrefix 3 ++ suffix) = .done 3 suffix := by
  simp

example : Derives headerPrefixFormat (writeHeaderPrefix 3 ++ suffix) 3 suffix := by
  exact derives_headerPrefix_iff.mpr rfl

example : takeHeaderPrefix (writeHeaderPrefix 4 |>.take 80) = .needMore (some 8) := by
  rfl

example : ∃ completion sectionCount,
    completion.length = 8 ∧
    takeHeaderPrefix ((writeHeaderPrefix 4).take 80 ++ completion) =
      .done sectionCount Vec.empty := by
  simpa [headerPrefixSize, canonicalPeOffset, peSignatureSize, coffHeaderSize] using
    takeHeaderPrefix_needMore_has_exact_completion
      ((writeHeaderPrefix 4).take 80) (some 8) (by rfl)

example : takeHeaderPrefix (Vec.fromList [0]) =
    .invalid (.malformed "impossible PE header prefix") := by
  rfl

private def arbitraryCountPrefix : Std.Logical.ByteArray :=
  writeHeaderPrefixLeading ++ Vec.fromList [0xaa]

example : takeHeaderPrefix arbitraryCountPrefix = .needMore (some 17) := by
  rfl

private def badMagic : Std.Logical.ByteArray :=
  Vec.fromList [0] ++ (writeHeaderPrefix 1).drop 1

example : takeHeaderPrefix badMagic =
    .invalid (.malformed "noncanonical PE header prefix") := by
  rfl

end Grass.Tests.Artifact.PE.HeaderReader
