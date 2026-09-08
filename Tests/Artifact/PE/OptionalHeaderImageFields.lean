import Grass.Artifact.PE.OptionalHeaderImageFields

/-! # PE32+ optional-header image-field fixtures -/

namespace Grass.Tests.Artifact.PE.OptionalHeaderImageFields

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def fields : Grass.Artifact.PE.OptionalHeaderImageFields := {
  win32VersionValue := 0
  sizeOfImage := 0x3000
  sizeOfHeaders := 0x400
  checkSum := 0x12345678
}

example : writeOptionalHeaderImageFields fields = Vec.fromList [
    0x00, 0x00, 0x00, 0x00,
    0x00, 0x30, 0x00, 0x00,
    0x00, 0x04, 0x00, 0x00,
    0x78, 0x56, 0x34, 0x12] := by
  decide

example : readOptionalHeaderImageFields Vec.empty =
    .needMore (some 16) := by
  exact readOptionalHeaderImageFields_short (by decide)

example : (writeOptionalHeaderImageFields fields).length = 16 := by simp

example : readOptionalHeaderImageFields
    (writeOptionalHeaderImageFields fields ++ Vec.singleton 0xaa) =
      .done fields (Vec.singleton 0xaa) := by
  simp

example : Derives optionalHeaderImageFieldsFormat
    (writeOptionalHeaderImageFields fields) fields Vec.empty :=
  writeOptionalHeaderImageFields_derives fields

end Grass.Tests.Artifact.PE.OptionalHeaderImageFields
