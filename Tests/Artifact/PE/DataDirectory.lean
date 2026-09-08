import Grass.Artifact.PE.DataDirectory

/-! # PE data-directory fixtures -/

namespace Grass.Tests.Artifact.PE.DataDirectory

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def exportDirectory : Grass.Artifact.PE.DataDirectory :=
  ⟨0x10203040, 0x50607080⟩

def zeroDirectory : Grass.Artifact.PE.DataDirectory := ⟨0, 0⟩

def canonicalDirectories : Vec Grass.Artifact.PE.DataDirectory :=
  Vec.fromList (exportDirectory :: List.replicate 15 zeroDirectory)

theorem canonicalDirectories_length : canonicalDirectories.length = 16 := by
  decide

def canonicalTable : DataDirectoryTable :=
  ⟨canonicalDirectories, canonicalDirectories_length⟩

example : writeDataDirectory exportDirectory =
    Vec.fromList [0x40, 0x30, 0x20, 0x10, 0x80, 0x70, 0x60, 0x50] := by
  decide

example : readDataDirectory (Vec.fromList [0x40, 0x30, 0x20]) =
    .needMore (some 5) := by
  exact readDataDirectory_short (by decide)

example : (writeDataDirectoryTable canonicalTable).length = 128 := by simp

example : readDataDirectoryTable Vec.empty = .needMore (some 128) := by
  exact readDataDirectoryTable_short (by decide)

example : readDataDirectoryTable
    (writeDataDirectoryTable canonicalTable ++ Vec.fromList [0xaa, 0xbb]) =
      .done canonicalTable (Vec.fromList [0xaa, 0xbb]) := by
  simp

example : Derives dataDirectoryTableFormat
    (writeDataDirectoryTable canonicalTable) canonicalTable Vec.empty :=
  writeDataDirectoryTable_derives canonicalTable

end Grass.Tests.Artifact.PE.DataDirectory
