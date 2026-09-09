import Grass.Artifact.PE.ImageWriter
import Grass.Std.Logical.HostBytes

/-!
# Windows loader smoke probe for the owned PE writer

Run with `lake env lean --run Tests/Artifact/PE/RunImage.lean`. The probe
refuses off x86-64 Windows, writes only beneath the host temporary directory,
executes images emitted by `Grass.Artifact.PE.writeImage`, and requires distinct
processor-visible statuses from the import-free and loader-resolved paths.
-/

namespace Grass.Tests.Artifact.PE.RunImage

open Grass.Std.Logical Grass.Artifact.PE

private def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

/-- `mov eax, 42; ret`: opaque adapter input here, not an instruction-encoding
claim by the artifact layer. -/
private def returnEntryBytes : Std.Logical.ByteArray :=
  Vec.fromList [0xb8, 0x29, 0, 0, 0, 0xc3]

private def returnDescription : ExecutableImageDescription :=
  { entryPointRva := 4096
    sections := Vec.fromList
      [{ name := textName
         contents := returnEntryBytes
         characteristics := 0x60000020 }]
    imports := Vec.empty }

private theorem returnReady : returnDescription.WriteReady := by decide

private def exitProcess : ImportSymbol :=
  ⟨Vec.fromList [69, 120, 105, 116, 80, 114, 111, 99, 101, 115, 115]⟩

private def kernel32 : ImportLibrary :=
  { name := Vec.fromList [107, 101, 114, 110, 101, 108, 51, 50, 46, 100, 108, 108]
    symbols := Vec.fromList [exitProcess] }

/-- `sub rsp, 40; mov ecx, 42; call [rip + 0x1019]`. The displacement reaches
the synthesized first IAT slot at RVA `0x2028` from instruction end `0x100f`.
The bytes remain opaque input to the artifact layer. -/
private def importEntryBytes : Std.Logical.ByteArray :=
  Vec.fromList
    [0x48, 0x83, 0xec, 0x28, 0xb9, 0x2a, 0, 0, 0, 0xff, 0x15, 0x19, 0x10, 0, 0]

private def importDescription : ExecutableImageDescription :=
  { entryPointRva := 4096
    sections := Vec.fromList
      [{ name := textName
         contents := importEntryBytes
         characteristics := 0x60000020 }]
    imports := Vec.fromList [kernel32] }

set_option maxRecDepth 4096 in
private theorem importReady : importDescription.WriteReady := by decide

private def scratchDir : IO System.FilePath := do
  let base ← match (← IO.getEnv "TEMP") with
    | some path => pure (System.FilePath.mk path)
    | none => throw (IO.userError
        "TEMP is unavailable; refusing to write an executable into the checkout")
  pure base

/-- Execute both the import-free return path and the loader-resolved import
path, failing unless each reports its distinct expected status. -/
def run : IO UInt32 := do
  if !(System.Platform.isWindows && System.Platform.numBits == 64) then
    IO.eprintln "PE loader probe refused: requires x86-64 Windows"
    return 1
  let scratch ← scratchDir
  let basePath := scratch / "grass-g-build-pe-smoke.exe"
  IO.FS.writeBinFile basePath (writeImage returnDescription returnReady).toHostBytes
  let baseOutput ← IO.Process.output { cmd := basePath.toString, args := #[] }
  IO.FS.removeFile basePath
  if baseOutput.exitCode != 41 then
    IO.eprintln s!"PE loader probe failed: import-free image exited {baseOutput.exitCode}"
    return 1
  let importPath := scratch / "grass-g-build-pe-import-smoke.exe"
  IO.FS.writeBinFile importPath (writeImage importDescription importReady).toHostBytes
  let importOutput ← IO.Process.output { cmd := importPath.toString, args := #[] }
  IO.FS.removeFile importPath
  if importOutput.exitCode != 42 then
    IO.eprintln s!"PE loader probe failed: imported ExitProcess image exited {importOutput.exitCode}"
    return 1
  IO.println "PE loader probes passed: import-free image exited 41; ExitProcess image exited 42"
  return 0

end Grass.Tests.Artifact.PE.RunImage

def main : IO UInt32 := Grass.Tests.Artifact.PE.RunImage.run
