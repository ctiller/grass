import Grass.Artifact.COFF.SectionHeader

/-! # COFF section-header fixtures -/

namespace Grass.Tests.Artifact.COFF.SectionHeader

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

def textName : SizedByteArray 8 :=
  ⟨Vec.fromList [0x2e, 0x74, 0x65, 0x78, 0x74, 0x00, 0x00, 0x00], by decide⟩

def textSection : SectionHeader where
  name := textName
  physicalAddressOrVirtualSize := 0
  virtualAddress := 0
  sizeOfRawData := 0x10
  pointerToRawData := 0x3c
  pointerToRelocations := 0x4c
  pointerToLineNumbers := 0
  numberOfRelocations := 1
  numberOfLineNumbers := 0
  characteristics := 0x60500020

def encodedTextSection : Std.Logical.ByteArray := Vec.fromList [
  0x2e, 0x74, 0x65, 0x78, 0x74, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x10, 0x00, 0x00, 0x00, 0x3c, 0x00, 0x00, 0x00,
  0x4c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x01, 0x00, 0x00, 0x00, 0x20, 0x00, 0x50, 0x60]

example : writeSectionHeader textSection = encodedTextSection := by decide

example : readSectionHeader encodedTextSection =
    .done textSection Vec.empty := by rfl

example : readSectionHeader
    (encodedTextSection ++ Vec.fromList [0xaa, 0xbb]) =
    .done textSection (Vec.fromList [0xaa, 0xbb]) := by rfl

example : readSectionHeader Vec.empty = .needMore (some 40) := by rfl

example : readSectionHeader (Vec.fromList [0x2e, 0x74, 0x65]) =
    .needMore (some 37) := by rfl

example : (writeSectionHeader textSection).length = 40 := by
  exact length_writeSectionHeader textSection

example : Derives sectionHeaderFormat (writeSectionHeader textSection)
    textSection Vec.empty := by
  exact writeSectionHeader_derives textSection

end Grass.Tests.Artifact.COFF.SectionHeader
