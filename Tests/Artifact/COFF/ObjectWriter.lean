import Grass.Artifact.COFF.ObjectWriter
import Tests.Artifact.COFF.Object

/-! # Canonical COFF object-writer fixtures -/

namespace Grass.Tests.Artifact.COFF.ObjectWriter

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.COFF.Layout
open Grass.Tests.Artifact.COFF.Object
open Grass.Tests.Artifact.COFF.Relocation
open Grass.Tests.Artifact.COFF.SectionHeader
open Grass.Tests.Artifact.COFF.StringTable
open Grass.Tests.Artifact.COFF.Symbol
open Grass.Tests.Artifact.COFF.SymbolValidation

def textDescription : SectionDescription where
  name := textName
  physicalAddressOrVirtualSize := 0
  virtualAddress := 0
  rawData := objectRawData.1
  relocations := Vec.singleton rawRelocation
  lineNumbers := Vec.empty
  characteristics := layoutSection.characteristics

def objectDescription : ObjectDescription where
  machine := layoutHeader.machine
  timeDateStamp := 0
  characteristics := 0
  sections := Vec.singleton textDescription
  symbols := .present (Vec.singleton mainCell) longNames

example : objectDescription.sectionLayout.1 = layoutSections := by decide

example : objectDescription.header = layoutHeader := by decide

example : objectDescription.header.numberOfSections.toNat = 1 := by
  exact objectDescription.header_numberOfSections (by decide)

example : objectDescription.header.numberOfSymbols.toNat = 1 := by
  exact objectDescription.header_numberOfSymbols (by decide)

example : objectDescription.header.pointerToSymbolTable.toNat = 86 := by
  exact objectDescription.header_pointerToSymbolTable_present
    (Vec.singleton mainCell) longNames (by rfl) (by decide)

example : (textDescription.headerAt 60).sizeOfRawData.toNat =
    textDescription.rawData.length := by
  exact textDescription.headerAt_sizeOfRawData 60 (by decide)

example : (textDescription.headerAt 60).pointerToRawData.toNat = 60 := by
  exact textDescription.headerAt_pointerToRawData_of_pos 60 (by decide)
    (by decide)

example : (textDescription.headerAt 60).pointerToRelocations.toNat = 76 := by
  exact textDescription.headerAt_pointerToRelocations_of_pos 60 (by decide)
    (by decide)

example : (textDescription.headerAt 60).pointerToLineNumbers.toNat = 0 := by
  exact textDescription.headerAt_pointerToLineNumbers_of_empty 60 (by rfl)

example : (textDescription.headerAt 60).PointersCoherent := by
  exact textDescription.headerAt_pointersCoherent 60 (by decide) (by decide)
    (by decide) (by decide) (by decide)

def textContents : SectionContents :=
  textDescription.contentsAt 60 (by decide) (by decide) (by decide)

example : textContents.header = textDescription.headerAt 60 := by rfl

example : textContents.rawData.1 = textDescription.rawData := by rfl

example : textContents.relocations.relocations = textDescription.relocations := by
  rfl

example : textContents.lineNumbers.lines = textDescription.lineNumbers := by rfl

def fullyPopulatedDescription : SectionDescription :=
  { textDescription with
    lineNumbers := Vec.singleton (.functionSymbolIndex 3) }

example :
    readSectionContents (fullyPopulatedDescription.headerAt 4)
        (Vec.replicate 4 0 ++
          writeSectionDescription fullyPopulatedDescription ++
          Vec.singleton 0xff) =
      .done (fullyPopulatedDescription.contentsAt 4 (by decide) (by decide)
        (by decide)) Vec.empty := by
  exact readSectionContents_writeSectionDescription_append_of_pos
    fullyPopulatedDescription 4 (Vec.replicate 4 0) (Vec.singleton 0xff)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

example :
    readSectionContents (textDescription.headerAt 4)
        (Vec.replicate 4 0 ++ writeSectionDescription textDescription ++
          Vec.singleton 0xff) =
      .done (textDescription.contentsAt 4 (by decide) (by decide) (by decide))
        Vec.empty := by
  exact readSectionContents_writeSectionDescription_append textDescription 4
    (Vec.replicate 4 0) (Vec.singleton 0xff) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def emptySectionDescription : SectionDescription :=
  { textDescription with
    rawData := Vec.empty
    relocations := Vec.empty
    lineNumbers := Vec.empty }

example :
    readSectionContents (emptySectionDescription.headerAt 4)
        (Vec.replicate 4 0 ++ writeSectionDescription emptySectionDescription ++
          Vec.singleton 0xff) =
      .done (emptySectionDescription.contentsAt 4 (by decide) (by decide)
        (by decide)) Vec.empty := by
  exact readSectionContents_writeSectionDescription_append
    emptySectionDescription 4 (Vec.replicate 4 0) (Vec.singleton 0xff)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : objectDescription.Writable = true := by decide

example : (objectDescription.contents (by decide)).map SectionContents.header =
    objectDescription.sectionLayout.1 := by
  exact objectDescription.contents_headers (by decide)

example :
    readSectionContentsList objectDescription.sectionLayout.1.toList
        objectDescription.bytes =
      .done (objectDescription.contents (by decide)).toList Vec.empty := by
  exact objectDescription.readSectionContentsList_bytes (by decide)

example : (writeSectionDescription textDescription).length =
    textDescription.byteLength := by
  exact length_writeSectionDescription textDescription

example : objectDescription.sectionLayout.2 =
    20 + 40 * objectDescription.sections.length +
      objectDescription.sectionsByteLength := by
  exact objectDescription.end_sectionLayout

example : objectDescription.bytes.length = objectDescription.byteLength := by
  exact objectDescription.length_bytes

theorem writeObjectDescription_objectDescription :
    writeObjectDescription objectDescription = .ok objectDescription.bytes := by
  have widths : objectDescription.widthsFit = true := by decide
  have symbols : objectDescription.symbols =
      .present (Vec.singleton mainCell) longNames := by rfl
  have auxiliary : validAuxLayoutScan 1 [mainCell] = true := by rfl
  have names : validPrimaryNamesScan 1 [mainCell] longNames = true := by rfl
  simp only [writeObjectDescription, widths, if_true, symbols]
  rfl

example : objectDescription.Writable = true :=
  (writeObjectDescription_ok_iff objectDescription).mp
    writeObjectDescription_objectDescription

example : objectDescription.bytes.length = objectDescription.byteLength ∧
    objectDescription.byteLength < 2 ^ 32 :=
  writeObjectDescription_ok_length writeObjectDescription_objectDescription

theorem objectDescription_bytes : objectDescription.bytes = encodedObject := by
  unfold ObjectDescription.bytes
  rw [show objectDescription.sectionLayout = (layoutSections, 86) by decide]
  rw [show objectDescription.header = layoutHeader by decide]
  rfl

example : readObject objectDescription.bytes = .done expectedObject Vec.empty := by
  rw [objectDescription_bytes]
  exact readObject_encodedObject

def absentDescription : ObjectDescription :=
  { objectDescription with symbols := .absent }

example : writeObjectDescription absentDescription = .ok noSymbolsObject := by
  rfl

def invalidAuxDescription : ObjectDescription :=
  { objectDescription with
    symbols := .present
      (Vec.fromList [{ mainCell with numberOfAuxSymbols := 2 }, mainCell])
      longNames }

example : writeObjectDescription invalidAuxDescription =
    .error (.malformed "COFF auxiliary symbol layout is inconsistent") := by
  rfl

def invalidNameCell : SymbolCell :=
  { mainCell with
    rawName := ⟨Vec.fromList [0, 0, 0, 0, 9, 0, 0, 0], by rfl⟩ }

def invalidNameDescription : ObjectDescription :=
  { objectDescription with
    symbols := SymbolDescription.present (Vec.singleton invalidNameCell)
      longNames }

example : writeObjectDescription invalidNameDescription =
    .error (.malformed "COFF primary symbol name is invalid") := by
  rfl

end Grass.Tests.Artifact.COFF.ObjectWriter
