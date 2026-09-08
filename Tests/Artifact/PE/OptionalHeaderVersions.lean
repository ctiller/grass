import Grass.Artifact.PE.OptionalHeaderVersions

/-! # PE32+ optional-header version fixtures -/

namespace Grass.Tests.Artifact.PE.OptionalHeaderVersions

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def versions : Grass.Artifact.PE.OptionalHeaderVersions := {
  majorOperatingSystemVersion := 6
  minorOperatingSystemVersion := 0
  majorImageVersion := 1
  minorImageVersion := 2
  majorSubsystemVersion := 6
  minorSubsystemVersion := 1
}

example : writeOptionalHeaderVersions versions = Vec.fromList [
    0x06, 0x00, 0x00, 0x00, 0x01, 0x00,
    0x02, 0x00, 0x06, 0x00, 0x01, 0x00] := by
  decide

example : readOptionalHeaderVersions Vec.empty = .needMore (some 12) := by
  exact readOptionalHeaderVersions_short (by decide)

example : (writeOptionalHeaderVersions versions).length = 12 := by simp

example : readOptionalHeaderVersions
    (writeOptionalHeaderVersions versions ++ Vec.singleton 0xaa) =
      .done versions (Vec.singleton 0xaa) := by
  simp

example : Derives optionalHeaderVersionsFormat
    (writeOptionalHeaderVersions versions) versions Vec.empty :=
  writeOptionalHeaderVersions_derives versions

end Grass.Tests.Artifact.PE.OptionalHeaderVersions
