import Grass.Artifact.PE.SectionTable

namespace Grass.Tests.Artifact.PE.SectionTable

open Grass.Std.Logical Grass.Artifact.PE

private def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

private def textSection : RawSection :=
  { name := textName
    contents := Vec.fromList [0x90, 0xc3]
    characteristics := 0x60000020 }

private def placedText : PlacedSection :=
  { source := textSection
    virtualSpan := ⟨4096, 2⟩
    rawSpan := ⟨512, 512⟩ }

example : textName.write = Vec.fromList [46, 116, 101, 120, 116, 0, 0, 0] := by
  decide

example : (writeSectionHeader placedText).length = 40 := by
  simp [sectionHeaderSize]

example : ((writeSectionHeader placedText).drop 8).take 16 =
    Vec.fromList [2, 0, 0, 0, 0, 16, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0] := by
  decide

example : (writeSectionTable (Vec.fromList [placedText, placedText])).length = 80 := by
  decide

end Grass.Tests.Artifact.PE.SectionTable
