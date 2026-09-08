import Grass.Artifact.COFF.StringTable

/-! # COFF string-table and symbol-offset fixtures -/

namespace Grass.Tests.Artifact.COFF.StringTable

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

def longPayload : Std.Logical.ByteArray :=
  Vec.fromList [0x6c, 0x6f, 0x6e, 0x67, 0x00]

def longNames : Grass.Artifact.COFF.StringTable where
  declaredSize := 9
  payload := longPayload
  minimumSize := by decide
  sizeMatches := by decide

def encodedLongNames : Std.Logical.ByteArray :=
  Vec.fromList [0x09, 0x00, 0x00, 0x00, 0x6c, 0x6f, 0x6e, 0x67, 0x00]

example : writeStringTable longNames = encodedLongNames := by decide

example : readStringTable encodedLongNames = .done longNames Vec.empty := by rfl

example : readStringTable (encodedLongNames ++ Vec.fromList [0xaa]) =
    .done longNames (Vec.fromList [0xaa]) := by rfl

example : readStringTable (Vec.fromList [0x09, 0x00, 0x00, 0x00, 0x6c]) =
    .needMore (some 4) := by rfl

example : readStringTable (Vec.fromList [0x03, 0x00, 0x00, 0x00]) =
    .invalid (.malformed "COFF string-table size is below four") := by rfl

example : longNames.ValidOffset 4 := by decide

example : longNames.ValidOffset 8 := by decide

example : ¬longNames.ValidOffset 3 := by decide

example : ¬longNames.ValidOffset 9 := by decide

example : (SymbolName.stringTableOffset 4).ValidIn longNames := by decide

example : Derives stringTableFormat (writeStringTable longNames)
    longNames Vec.empty := by
  exact writeStringTable_derives longNames

end Grass.Tests.Artifact.COFF.StringTable
