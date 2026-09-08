import Grass.Artifact.PE.Layout

namespace Grass.Tests.Artifact.PE.Layout

open Grass.Std.Logical Grass.Artifact.PE

private def shortName (byte : Byte) : SectionName :=
  ⟨Vec.fromList [byte], by simp [Vec.length]⟩

private def rawSection (nameByte : Byte) (contents : List Byte)
    (characteristics : BitVec 32) : RawSection :=
  { name := shortName nameByte
    contents := Vec.fromList contents
    characteristics }

private def twoSectionImage : ExecutableImageDescription :=
  { entryPointRva := 0x1000
    sections := Vec.fromList
      [ rawSection 1 [10, 11] 0x60000020,
        rawSection 2 [20, 21, 22] 0x40000040 ]
    imports := Vec.empty }

example : ntHeadersSize 1 = 304 := by decide

example : (ntHeadersSpan 128 1).endOffset = 432 := by decide

example : firstRawOffset 128 1 512 = 512 := by decide

/-- A fragment-local pseudo-header `[0,304)` appears disjoint from raw bytes
`[304,368)`, while the real NT span rooted at `e_lfanew = 128` is `[128,432)`
and overlaps them. This is the regression for the coordinate-system defect. -/
theorem fragment_local_disjoint_but_absolute_overlaps :
    (FileSpan.Disjoint ⟨0, ntHeadersSize 1⟩ ⟨304, 64⟩) ∧
    ¬ (FileSpan.Disjoint (ntHeadersSpan 128 1) ⟨304, 64⟩) := by
  decide

example : (placeRawSections twoSectionImage 512).length = 2 := by decide

example : ((placeRawSections twoSectionImage 512).get? 0).map (·.rawSpan) = some ⟨512, 512⟩ := by
  decide

example : ((placeRawSections twoSectionImage 512).get? 1).map (·.rawSpan) = some ⟨1024, 512⟩ := by
  decide

end Grass.Tests.Artifact.PE.Layout
