import Grass.Artifact.ELF.ProgramHeader

namespace Tests.Artifact.ELF.ProgramHeader

open Grass.Artifact.ELF Grass.Grammar Grass.Std.Logical

def header : ProgramHeader64 :=
  ProgramHeader64.mk 1 5 0x40 0x400000 0x400000 0x200 0x300 0x1000

example : (writeProgramHeader64 header).length = 56 := writeProgramHeader64_length _

example : readProgramHeader64 (writeProgramHeader64 header ++ Vec.fromList [0xa5, 0x5a]) =
    .done header (Vec.fromList [0xa5, 0x5a]) :=
  readProgramHeader64_write_append _ _

/-- Check independent ELF64 program-header field offsets and little-endian bytes. -/
example : (writeProgramHeader64 header).get? 0 = some 1 := by decide
example : (writeProgramHeader64 header).get? 4 = some 5 := by decide
example : (writeProgramHeader64 header).get? 8 = some 0x40 := by decide
example : (writeProgramHeader64 header).get? 18 = some 0x40 := by decide
example : (writeProgramHeader64 header).get? 32 = some 0 := by decide
example : (writeProgramHeader64 header).get? 41 = some 3 := by decide
example : (writeProgramHeader64 header).get? 49 = some 0x10 := by decide

def truncated : Bool :=
  match readProgramHeader64 ((writeProgramHeader64 header).take 55) with
  | .needMore (some 1) => true
  | _ => false

example : truncated = true := by decide

end Tests.Artifact.ELF.ProgramHeader
