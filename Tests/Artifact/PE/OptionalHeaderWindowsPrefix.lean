import Grass.Artifact.PE.OptionalHeaderWindowsPrefix

/-! # PE32+ Windows-field prefix fixtures -/

namespace Grass.Tests.Artifact.PE.OptionalHeaderWindowsPrefix

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def fields : Grass.Artifact.PE.OptionalHeaderWindowsPrefix := {
  imageBase := 0x0000000140000000
  sectionAlignment := 0x1000
  fileAlignment := 0x200
}

example : writeOptionalHeaderWindowsPrefix fields = Vec.fromList [
    0x00, 0x00, 0x00, 0x40, 0x01, 0x00, 0x00, 0x00,
    0x00, 0x10, 0x00, 0x00,
    0x00, 0x02, 0x00, 0x00] := by
  decide

example : readOptionalHeaderWindowsPrefix Vec.empty =
    .needMore (some 16) := by
  exact readOptionalHeaderWindowsPrefix_short (by decide)

example : (writeOptionalHeaderWindowsPrefix fields).length = 16 := by simp

example : readOptionalHeaderWindowsPrefix
    (writeOptionalHeaderWindowsPrefix fields ++ Vec.fromList [0xaa, 0xbb]) =
      .done fields (Vec.fromList [0xaa, 0xbb]) := by
  simp

example : Derives optionalHeaderWindowsPrefixFormat
    (writeOptionalHeaderWindowsPrefix fields) fields Vec.empty :=
  writeOptionalHeaderWindowsPrefix_derives fields

end Grass.Tests.Artifact.PE.OptionalHeaderWindowsPrefix
