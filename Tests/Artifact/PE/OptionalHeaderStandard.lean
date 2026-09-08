import Grass.Artifact.PE.OptionalHeaderStandard

/-! # PE32+ optional-header standard-field fixtures -/

namespace Grass.Tests.Artifact.PE.OptionalHeaderStandard

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def standard : Grass.Artifact.PE.OptionalHeaderStandard := {
  majorLinkerVersion := 14
  minorLinkerVersion := 0
  sizeOfCode := 0x200
  sizeOfInitializedData := 0x400
  sizeOfUninitializedData := 0
  addressOfEntryPoint := 0x1000
  baseOfCode := 0x1000
}

example : writePE32PlusMagic () = Vec.fromList [0x0b, 0x02] := by decide

example : readPE32PlusMagic (Vec.fromList [0x0b]) =
    .needMore (some 1) := by
  exact readPE32PlusMagic_short (by decide)

example : readPE32PlusMagic (Vec.fromList [0x0b, 0x01]) =
    .invalid (.malformed "PE32+ optional-header magic mismatch") := by
  rfl

example : (writeOptionalHeaderStandard standard).length = 24 := by simp

example : readOptionalHeaderStandard Vec.empty = .needMore (some 24) := by
  exact readOptionalHeaderStandard_short (by decide)

example : readOptionalHeaderStandard
    (writeOptionalHeaderStandard standard ++ Vec.singleton 0xff) =
      .done standard (Vec.singleton 0xff) := by
  simp

example : Derives optionalHeaderStandardFormat
    (writeOptionalHeaderStandard standard) standard Vec.empty :=
  writeOptionalHeaderStandard_derives standard

end Grass.Tests.Artifact.PE.OptionalHeaderStandard
