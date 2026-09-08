import Grass.Artifact.PE.Description

namespace Grass.Tests.Artifact.PE.Description

open Grass.Std.Logical Grass.Artifact.PE

example : SectionName.ofBytes? (Vec.fromList [1, 2, 3]) = some ⟨Vec.fromList [1, 2, 3], by decide⟩ := by
  decide

example : SectionName.ofBytes? (Vec.fromList [0, 1, 2, 3, 4, 5, 6, 7, 8]) = none := by
  decide

/-- The adapter accepts encoded bytes without importing or interpreting x86. -/
def opaqueTextSection : RawSection :=
  { name := ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩
    contents := Vec.fromList [0x90, 0xc3]
    characteristics := 0x60000020 }

example : opaqueTextSection.contents.length = 2 := by decide

end Grass.Tests.Artifact.PE.Description
