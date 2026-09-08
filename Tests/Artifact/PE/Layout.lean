import Grass.Artifact.PE.Layout

namespace Grass.Tests.Artifact.PE.Layout

open Grass.Artifact.PE

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

end Grass.Tests.Artifact.PE.Layout
