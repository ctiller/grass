import Grass.Artifact.ELF.Target

/-! External-comparison fixture emitter for the ELF target writer.

Run `lake env lean --run Tests/Artifact/ELF/Target.lean OUTPUT_DIRECTORY`.
The independent probe under `probes/linux/elf_phoff.py` reads these artifacts;
this module deliberately makes no closed byte-layout assertions. -/

namespace Tests.Artifact.ELF
open Grass.Artifact.ELF

def sampleSection (tag : UInt8) : ElfSection :=
  { virtualAddress := 0x400000, bytes := [tag, 0xa5], sizeBound := by change 2 < widthBound; decide
    readable := true, writable := false, executable := true }

def fixture (tags : List UInt8) (bound : tags.length < 65536) : Artifact :=
  { entry := 0x400000, sections := tags.map sampleSection, phnumBound := by simpa using bound }

def writeFixture (output : System.FilePath) (name : String) (tags : List UInt8)
    (bound : tags.length < 65536) : IO Unit :=
  IO.FS.writeBinFile (output / (name ++ ".elf"))
    ⟨(write 183 (fixture tags bound)).toArray⟩

end Tests.Artifact.ELF

def main (args : List String) : IO Unit := do
  let output ← match args with
    | [directory] => pure (System.FilePath.mk directory)
    | _ => throw <| IO.userError "usage: Target.lean OUTPUT_DIRECTORY"
  IO.FS.createDirAll output
  Tests.Artifact.ELF.writeFixture output "target-zero" [] (by decide)
  Tests.Artifact.ELF.writeFixture output "target-one" [0x11] (by decide)
  Tests.Artifact.ELF.writeFixture output "target-two" [0x11, 0x22] (by decide)
  Tests.Artifact.ELF.writeFixture output "target-three" [0x11, 0x22, 0x33] (by decide)
