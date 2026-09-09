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
    symbols := Vec.fromList [⟨Vec.fromList [2]⟩] }

private def importedImage : ExecutableImageDescription :=
  { description with imports := Vec.fromList [requestedImport] }

set_option maxRecDepth 4096 in
example : importedImage.WriteReady := by decide

set_option maxRecDepth 10000 in
private def importedBytes : Std.Logical.ByteArray :=
  writeImage importedImage (by decide)

example : importedBytes.length = 1536 := by
  unfold importedBytes
  rw [length_writeImage]
  decide

set_option maxRecDepth 10000 in
example : (importedBytes.drop 208).take 8 =
    Vec.fromList [0, 32, 0, 0, 40, 0, 0, 0] := by decide

set_option maxRecDepth 10000 in
example : (importedBytes.drop 1024).take 4 = Vec.fromList [0x38, 0x20, 0, 0] := by
  decide

end Grass.Tests.Artifact.PE.ImageWriter
