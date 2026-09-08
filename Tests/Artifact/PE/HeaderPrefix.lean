import Grass.Artifact.PE.HeaderPrefix

namespace Grass.Tests.Artifact.PE.HeaderPrefix

open Grass.Std.Logical Grass.Artifact.PE

example : writeCanonicalDosHeader.length = 64 := by decide

example : writeCanonicalDosHeader.get? 0 = some 0x4d := by decide

example : writeCanonicalDosHeader.get? 1 = some 0x5a := by decide

example : writeCanonicalDosHeader.drop 60 = Vec.fromList [0x40, 0, 0, 0] := by decide

example : writePeSignature = Vec.fromList [0x50, 0x45, 0, 0] := by rfl

example : (writeImageCoffHeader (2 : BitVec 16)).length = 20 := by
  simp [coffHeaderSize]

example : (writeHeaderPrefix 2).length = 88 := by decide

end Grass.Tests.Artifact.PE.HeaderPrefix
