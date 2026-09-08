import Grass.Artifact.PE.OptionalHeaderRuntimeFields

/-! # PE32+ optional-header runtime-field fixtures -/

namespace Grass.Tests.Artifact.PE.OptionalHeaderRuntimeFields

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def fields : Grass.Artifact.PE.OptionalHeaderRuntimeFields := {
  subsystem := 3
  dllCharacteristics := 0x8160
  sizeOfStackReserve := 0x100000
  sizeOfStackCommit := 0x1000
  sizeOfHeapReserve := 0x100000
  sizeOfHeapCommit := 0x1000
  loaderFlags := 0
  numberOfRvaAndSizes := 16
}

example : (writeOptionalHeaderRuntimeFields fields).length = 44 := by simp

example : readOptionalHeaderRuntimeFields Vec.empty =
    .needMore (some 44) := by
  exact readOptionalHeaderRuntimeFields_short (by decide)

example : readOptionalHeaderRuntimeFields
    (writeOptionalHeaderRuntimeFields fields ++ Vec.fromList [0xaa, 0xbb]) =
      .done fields (Vec.fromList [0xaa, 0xbb]) := by
  simp

example : Derives optionalHeaderRuntimeFieldsFormat
    (writeOptionalHeaderRuntimeFields fields) fields Vec.empty :=
  writeOptionalHeaderRuntimeFields_derives fields

end Grass.Tests.Artifact.PE.OptionalHeaderRuntimeFields
