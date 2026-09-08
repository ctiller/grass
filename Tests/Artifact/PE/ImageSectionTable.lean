import Grass.Artifact.PE.ImageSectionTable
import Tests.Artifact.PE.ImageHeaders

/-! # PE32+ image section-table fixtures -/

namespace Grass.Tests.Artifact.PE.ImageSectionTable

open Grass.Artifact.COFF Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def textNameBytes : Std.Logical.ByteArray :=
  Vec.fromList [0x2e, 0x74, 0x65, 0x78, 0x74, 0x00, 0x00, 0x00]

theorem textNameBytes_length : textNameBytes.length = 8 := by decide

def textSection : SectionHeader where
  name := ⟨textNameBytes, textNameBytes_length⟩
  physicalAddressOrVirtualSize := 1
  virtualAddress := 0x1000
  sizeOfRawData := 0x200
  pointerToRawData := 0x200
  pointerToRelocations := 0
  pointerToLineNumbers := 0
  numberOfRelocations := 0
  numberOfLineNumbers := 0
  characteristics := 0x60000020

def table : Grass.Artifact.PE.ImageSectionTable where
  headers := Grass.Tests.Artifact.PE.ImageHeaders.headers
  sections := Vec.singleton textSection
  sectionCount := by rfl

example : (writeImageSectionTable table).length = 304 := by
  rw [length_writeImageSectionTable]
  rfl

example : readImageSectionTable
    (writeImageSectionTable table ++ Vec.singleton 0xaa) =
      .done table (Vec.singleton 0xaa) := by
  simp

example : Derives imageSectionTableFormat
    (writeImageSectionTable table) table Vec.empty :=
  writeImageSectionTable_derives table

end Grass.Tests.Artifact.PE.ImageSectionTable
