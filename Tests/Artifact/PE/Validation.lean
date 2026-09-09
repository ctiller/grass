import Grass.Artifact.PE.Validation

namespace Grass.Tests.Artifact.PE.Validation

open Grass.Std.Logical Grass.Artifact.PE

private def name : SectionName := ⟨Vec.fromList [1], by decide⟩

private def source : RawSection :=
  { name
    contents := Vec.fromList [0x90, 0xc3]
    characteristics := 0x60000020 }

private def smallImage : ExecutableImageDescription :=
  { entryPointRva := 4096
    sections := Vec.fromList [source]
    imports := Vec.empty }

example : smallImage.Writable := by decide

private def overflowingPlacement : PlacedSection :=
  { source
    virtualSpan := ⟨2 ^ 32, 1⟩
    rawSpan := ⟨512, 512⟩ }

example : placementFitsU32 overflowingPlacement = false := by decide

private def crossingPlacement : PlacedSection :=
  { source
    virtualSpan := ⟨2 ^ 32 - 1, 2⟩
    rawSpan := ⟨512, 512⟩ }

/-- Checking only each field separately would accept this placement; checking
the exclusive end rejects the interval that crosses the 32-bit boundary. -/
example : placementFitsU32 crossingPlacement = false := by decide

private def embeddedTerminator : ImportLibrary :=
  { name := Vec.fromList [65, 0, 66]
    symbols := Vec.fromList [⟨Vec.fromList [67]⟩] }

private def invalidImportImage : ExecutableImageDescription :=
  { smallImage with imports := Vec.fromList [embeddedTerminator] }

example : ¬invalidImportImage.Writable := by decide

end Grass.Tests.Artifact.PE.Validation
