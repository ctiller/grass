import Grass.Artifact.PE.ImageWriter
import Grass.Std.Logical.HostBytes

/-!
# Windows loader smoke probe for the owned PE writer

Run with `lake env lean --run Tests/Artifact/PE/RunImage.lean`. The probe
refuses off x86-64 Windows, writes only beneath the host temporary directory,
executes an image emitted by `Grass.Artifact.PE.writeImage`, and requires the
processor-visible exit status 42.
-/

namespace Grass.Tests.Artifact.PE.RunImage

open Grass.Std.Logical Grass.Artifact.PE

private def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

/-- `mov eax, 42; ret`: opaque adapter input here, not an instruction-encoding
claim by the artifact layer. -/
private def entryBytes : Std.Logical.ByteArray :=
  Vec.fromList [0xb8, 0x2a, 0, 0, 0, 0xc3]

private def description : ExecutableImageDescription :=
  { entryPointRva := 4096
    sections := Vec.fromList
      [{ name := textName
         contents := entryBytes
         characteristics := 0x60000020 }]
    imports := Vec.empty }

private theorem ready : description.WriteReady := by decide

private def scratchPath : IO System.FilePath := do
  let base ← match (← IO.getEnv "TEMP") with
    | some path => pure (System.FilePath.mk path)
    | none => throw (IO.userError
        "TEMP is unavailable; refusing to write an executable into the checkout")
  pure (base / "grass-g-build-pe-smoke.exe")

/-- Execute the emitted image and fail unless Windows reports exit status 42. -/
def run : IO UInt32 := do
  if !(System.Platform.isWindows && System.Platform.numBits == 64) then
    IO.eprintln "PE loader probe refused: requires x86-64 Windows"
    return 1
  let path ← scratchPath
  IO.FS.writeBinFile path (writeImage description ready).toHostBytes
  let output ← IO.Process.output { cmd := path.toString, args := #[] }
  IO.FS.removeFile path
  if output.exitCode == 42 then
    IO.println "PE loader probe passed: emitted image exited 42"
    return 0
  IO.eprintln s!"PE loader probe failed: emitted image exited {output.exitCode}"
  return 1

end Grass.Tests.Artifact.PE.RunImage

def main : IO UInt32 := Grass.Tests.Artifact.PE.RunImage.run
