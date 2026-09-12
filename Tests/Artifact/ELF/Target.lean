import Grass.Artifact.ELF.Target

namespace Tests.Artifact.ELF
open Grass.Artifact.ELF

/-- Arbitrary short payloads exercise differing table counts and payload starts. -/
def sampleSection (tag : UInt8) : ElfSection :=
  { virtualAddress := 0x400000, bytes := [tag, 0xa5], sizeBound := by change 2 < widthBound; decide
    readable := true, writable := false, executable := true }

def fixture (tags : List UInt8) (bound : tags.length < 65536) : Artifact :=
  { entry := 0x400000, sections := tags.map sampleSection, phnumBound := by simpa using bound }

-- These comparisons inspect literal field offsets and bytes, not ELF.read.
example : ((write 183 (fixture [] (by decide))).drop 32).take 8 =
    [0, 0, 0, 0, 0, 0, 0, 0] := by decide
example : (write 183 (fixture [] (by decide))).length = 64 := by decide

example : ((write 183 (fixture [0x11] (by decide))).drop 32).take 8 =
    [64, 0, 0, 0, 0, 0, 0, 0] := by decide
example : ((write 183 (fixture [0x11] (by decide))).drop 64).take 4 =
    [1, 0, 0, 0] := by decide
example : ((write 183 (fixture [0x11] (by decide))).drop 72).take 8 =
    [120, 0, 0, 0, 0, 0, 0, 0] := by decide
example : (write 183 (fixture [0x11] (by decide))).drop 120 = [0x11, 0xa5] := by decide

example : ((write 62 (fixture [0x11, 0x22] (by decide))).drop 32).take 8 =
    [64, 0, 0, 0, 0, 0, 0, 0] := by decide
example : ((write 62 (fixture [0x11, 0x22] (by decide))).drop 120).take 4 =
    [1, 0, 0, 0] := by decide
example : ((write 62 (fixture [0x11, 0x22] (by decide))).drop 128).take 8 =
    [178, 0, 0, 0, 0, 0, 0, 0] := by decide
example : (write 62 (fixture [0x11, 0x22] (by decide))).drop 176 =
    [0x11, 0xa5, 0x22, 0xa5] := by decide

example : ((write 183 (fixture [0x11, 0x22, 0x33] (by decide))).drop 32).take 8 =
    [64, 0, 0, 0, 0, 0, 0, 0] := by decide
example : ((write 183 (fixture [0x11, 0x22, 0x33] (by decide))).drop 176).take 4 =
    [1, 0, 0, 0] := by decide
example : (write 183 (fixture [0x11, 0x22, 0x33] (by decide))).drop 232 =
    [0x11, 0xa5, 0x22, 0xa5, 0x33, 0xa5] := by decide

#print axioms Grass.Artifact.ELF.write_phoff_bytes
#print axioms Grass.Artifact.ELF.write_table_position
#print axioms Grass.Artifact.ELF.read_write

end Tests.Artifact.ELF
