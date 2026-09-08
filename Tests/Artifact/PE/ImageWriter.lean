import Grass.Artifact.PE.ImageWriter

namespace Grass.Tests.Artifact.PE.ImageWriter

open Grass.Std.Logical Grass.Artifact.PE

private def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

private def text : RawSection :=
  { name := textName
    contents := Vec.fromList [0x90, 0xc3]
    characteristics := 0x60000020 }

private def description : ExecutableImageDescription :=
  { entryPointRva := 4096
    sections := Vec.fromList [text]
    imports := Vec.empty }

private theorem ready : description.WriteReady := by decide

private def image : Std.Logical.ByteArray := writeImage description ready

example : image.length = 1024 := by
  unfold image
  rw [length_writeImage]
  decide

example : image.take 2 = Vec.fromList [0x4d, 0x5a] := by decide

example : (image.drop 60).take 4 = Vec.fromList [0x40, 0, 0, 0] := by decide

example : (image.drop 64).take 4 = Vec.fromList [0x50, 0x45, 0, 0] := by decide

set_option maxRecDepth 4096 in
example : (image.drop 512).take 2 = Vec.fromList [0x90, 0xc3] := by decide

set_option maxRecDepth 4096 in
example : (image.drop 514).take 510 = Vec.replicate 510 0 := by decide

private def requestedImport : ImportLibrary :=
  { name := Vec.fromList [1]
    symbols := Vec.empty }

private def prematureImportImage : ExecutableImageDescription :=
  { description with imports := Vec.fromList [requestedImport] }

/-- A requested import cannot be silently replaced by the optional header's
currently zero data-directory entries. -/
example : ¬prematureImportImage.WriteReady := by decide

end Grass.Tests.Artifact.PE.ImageWriter
