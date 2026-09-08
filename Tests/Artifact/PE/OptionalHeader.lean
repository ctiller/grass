import Grass.Artifact.PE.OptionalHeader

namespace Grass.Tests.Artifact.PE.OptionalHeader

open Grass.Std.Logical Grass.Artifact.PE

private def name : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

private def source : RawSection :=
  { name
    contents := Vec.fromList [0x90, 0xc3]
    characteristics := 0x60000020 }

private def description : ExecutableImageDescription :=
  { entryPointRva := 4096
    sections := Vec.fromList [source]
    imports := Vec.empty }

private def placed : Vec PlacedSection := placeImageSections description

example : (writeOptionalHeader description placed).length = 240 := by
  simp [optionalHeader64Size]

example : (writeOptionalHeader description placed).take 2 = Vec.fromList [0x0b, 0x02] := by
  decide

example : ((writeOptionalHeader description placed).drop 16).take 4 =
    Vec.fromList [0, 16, 0, 0] := by
  decide

example : ((writeOptionalHeader description placed).drop 56).take 8 =
    Vec.fromList [0, 32, 0, 0, 0, 2, 0, 0] := by
  decide

example : (writeOptionalHeader description placed).drop 112 = Vec.replicate 128 0 := by
  decide

end Grass.Tests.Artifact.PE.OptionalHeader
