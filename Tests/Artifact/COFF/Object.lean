import Grass.Artifact.COFF.Object
import Tests.Artifact.COFF.Layout
import Tests.Artifact.COFF.Relocation
import Tests.Artifact.COFF.Symbol
import Tests.Artifact.COFF.SymbolValidation

/-! # Complete COFF relocatable-object reader fixtures -/

namespace Grass.Tests.Artifact.COFF.Object

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.COFF.Layout
open Grass.Tests.Artifact.COFF.Relocation
open Grass.Tests.Artifact.COFF.StringTable
open Grass.Tests.Artifact.COFF.Symbol
open Grass.Tests.Artifact.COFF.SymbolValidation

def objectTable : SectionTable where
  header := layoutHeader
  sections := layoutSections
  sectionCount := by rfl

def objectRawData : SectionRawData layoutSection :=
  ⟨Vec.fromList [0x48, 0x31, 0xc0, 0xc3, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0], by rfl⟩

def objectRelocations : RelocationBlock layoutSection where
  relocations := Vec.singleton rawRelocation
  relocationCount := by rfl

def objectLineNumbers : LineNumberBlock layoutSection where
  lines := Vec.empty
  lineCount := by rfl

def objectSectionContents : SectionContents where
  header := layoutSection
  rawData := objectRawData
  relocations := objectRelocations
  lineNumbers := objectLineNumbers

def objectSymbolTable : SymbolTable layoutHeader where
  cells := Vec.singleton mainCell
  cellCount := by rfl

def objectValidatedSymbols : AuxValidatedSymbolTable layoutHeader where
  table := objectSymbolTable
  auxLayoutValid := by decide

def encodedObject : Std.Logical.ByteArray :=
  writeSectionTable objectTable ++
  writeSectionRawData objectRawData ++
  writeRelocationBlock objectRelocations ++
  writeAuxValidatedSymbolTable objectValidatedSymbols ++
  writeStringTable longNames

def expectedObject : Grass.Artifact.COFF.Object where
  bytes := encodedObject
  table := objectTable
  contents := Vec.singleton objectSectionContents
  contentHeaders := by rfl
  symbols := .present (by decide) objectValidatedSymbols longNames (by rfl)
  layoutValid := by decide

example : encodedObject.length = 113 := by decide

theorem readObject_encodedObject :
    readObject encodedObject = .done expectedObject Vec.empty := by
  rfl

example : readSectionContentsList [layoutSection] encodedObject =
    .done [objectSectionContents] Vec.empty := by
  have reads : ∀ content ∈ [objectSectionContents],
      readSectionContents content.header encodedObject =
        .done content Vec.empty := by
    intro content member
    simp only [List.mem_singleton] at member
    subst content
    rfl
  simpa [objectSectionContents] using
    readSectionContentsList_of_reads [objectSectionContents] encodedObject reads

def noSymbolsHeader : Header :=
  { layoutHeader with pointerToSymbolTable := 0, numberOfSymbols := 0 }

def noSymbolsTable : SectionTable where
  header := noSymbolsHeader
  sections := layoutSections
  sectionCount := by rfl

def noSymbolsObject : Std.Logical.ByteArray :=
  writeSectionTable noSymbolsTable ++
  writeSectionRawData objectRawData ++
  writeRelocationBlock objectRelocations

def noSymbolsExpected : Grass.Artifact.COFF.Object where
  bytes := noSymbolsObject
  table := noSymbolsTable
  contents := Vec.singleton objectSectionContents
  contentHeaders := by rfl
  symbols := .absent (by decide) (by decide)
  layoutValid := by decide

example : readObject noSymbolsObject =
    .done noSymbolsExpected Vec.empty := by
  rfl

def optionalHeader : Header :=
  { layoutHeader with sizeOfOptionalHeader := 2 }

def optionalTable : SectionTable where
  header := optionalHeader
  sections := layoutSections
  sectionCount := by rfl

example : readObject (writeSectionTable optionalTable) =
    .invalid (.unsupported "COFF relocatable object optional header") := by
  rfl

def overlappingObjectSection : SectionHeader :=
  { layoutSection with pointerToRawData := 50 }

def overlappingObjectTable : SectionTable where
  header := layoutHeader
  sections := Vec.singleton overlappingObjectSection
  sectionCount := by rfl

def overlappingObject : Std.Logical.ByteArray :=
  writeSectionTable overlappingObjectTable ++
  writeSectionRawData objectRawData ++
  writeRelocationBlock objectRelocations ++
  writeAuxValidatedSymbolTable objectValidatedSymbols ++
  writeStringTable longNames

example : readObject overlappingObject =
    .invalid (.malformed "COFF object spans overlap or exceed the file") := by
  rfl

def invalidNameObject : Std.Logical.ByteArray :=
  writeSectionTable objectTable ++
  writeSectionRawData objectRawData ++
  writeRelocationBlock objectRelocations ++
  writeSymbol invalidLongSymbol ++
  writeStringTable longNames

example : readObject invalidNameObject =
    .invalid (.malformed "COFF primary symbol name is invalid") := by
  rfl

end Grass.Tests.Artifact.COFF.Object
