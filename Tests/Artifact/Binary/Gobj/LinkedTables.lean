import Grass.Artifact.Binary.Gobj.LinkedTables

/-! # Cross-table `.gobj` validation fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.LinkedTables

open Grass.Artifact.Binary Grass.Artifact.Binary.Gobj Grass.Grammar
  Grass.Std.Logical

def sectionName : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x2e, 0x74], by decide⟩

def sectionContents : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x90, 0x90, 0xc3], by decide⟩

def profileId : GobjRelocationProfileId where
  owner := sectionName
  name := sectionName
  version := 1

def sectionEntry : GobjSection where
  name := sectionName
  alignment := ⟨0, by decide⟩
  permissions := ⟨5, by decide⟩
  profile := .relocatable profileId
  contents := sectionContents

def sections : GobjSectionTable := ⟨Vec.singleton sectionEntry, by decide⟩

def symbolName : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x66], by decide⟩

def symbolNominalName : GobjNominalId := ⟨⟨Vec.empty, by decide⟩, symbolName⟩

def symbolEntry : GobjSymbol where
  name := symbolNominalName
  body := .defined {
    binding := .exported
    sectionIndex := 0
    offset := 1
    size := 2
    extentFits := by decide }

def symbols : GobjSymbolTable where
  entries := Vec.singleton symbolEntry
  countFits := by decide
  namesUnique := by decide

def relocationEntry : GobjRelocation where
  sectionIndex := 0
  offset := 1
  targetSymbolIndex := 0
  kind := 7
  addend := 0

def relocations : GobjRelocationTable :=
  ⟨Vec.singleton relocationEntry, by decide⟩

example : symbols.ValidForSections sections := by decide
example : relocations.IndicesValid sections symbols := by decide
example : relocations.LocationsValidFor sections := by decide

def imports : GobjImportManifest where
  entries := Vec.empty
  countFits := by decide
  localTargetsUnique := by decide
  canonicallyOrdered := by decide

def tables : GobjLinkedTables where
  sections := sections
  symbols := symbols
  relocations := relocations
  imports := imports
  symbolExtentsValid := by decide
  symbolImportsValid := by decide
  allImportsUsed := by decide
  relocationIndicesValid := by decide
  relocationLocationsValid := by decide

def scope : SizedByteArray 16 := ⟨Vec.replicate 16 0, by simp⟩
def emptyBody : U32LengthPrefixedBytes := ⟨Vec.empty, by decide⟩

def payload : GobjPayload where
  formatVersion := .v1
  scope := scope
  sections := emptyBody
  symbols := emptyBody
  relocations := emptyBody
  imports := emptyBody
  sourceMap := emptyBody

theorem sectionsFit : (writeGobjSectionTable sections).length < 2 ^ 32 := by
  rw [length_writeGobjSectionTable]
  decide

theorem symbolsFit : (writeGobjSymbolTable symbols).length < 2 ^ 32 := by
  rw [length_writeGobjSymbolTable]
  decide

theorem relocationsFit :
    (writeGobjRelocationTable relocations).length < 2 ^ 32 := by
  rw [length_writeGobjRelocationTable]
  decide

theorem importsFit : (writeGobjImportManifest imports).length < 2 ^ 32 := by
  decide

example : parseGobjLinkedTables
    (payload.withLinkedTables tables sectionsFit symbolsFit relocationsFit
      importsFit) =
      .ok tables := by
  exact parseGobjLinkedTables_withLinkedTables payload tables sectionsFit
    symbolsFit relocationsFit importsFit

def outOfBoundsSymbol : GobjSymbol :=
  { symbolEntry with body := .defined {
      binding := .exported, sectionIndex := 0, offset := 2, size := 2,
      extentFits := by decide } }

def badSymbols : GobjSymbolTable where
  entries := Vec.singleton outOfBoundsSymbol
  countFits := by decide
  namesUnique := by decide

example : ¬ badSymbols.ValidForSections sections := by decide

def missingSectionSymbol : GobjSymbol :=
  { symbolEntry with body := .defined {
      binding := .exported, sectionIndex := 1, offset := 1, size := 2,
      extentFits := by decide } }

def missingSectionSymbols : GobjSymbolTable where
  entries := Vec.singleton missingSectionSymbol
  countFits := by decide
  namesUnique := by decide

example : ¬ missingSectionSymbols.ValidForSections sections := by decide

def badLocation : GobjRelocationTable :=
  ⟨Vec.singleton { relocationEntry with offset := 3 }, by decide⟩

example : ¬ badLocation.LocationsValidFor sections := by decide

def badReference : GobjRelocationTable :=
  ⟨Vec.singleton { relocationEntry with targetSymbolIndex := 1 }, by decide⟩

example : ¬ badReference.IndicesValid sections symbols := by decide

def importedEntry : GobjImportEntry where
  localTarget := symbolNominalName
  subject := .callable symbolNominalName symbolNominalName
  abiContract := symbolNominalName

def oneImport : GobjImportManifest where
  entries := Vec.singleton importedEntry
  countFits := by decide
  localTargetsUnique := by decide
  canonicallyOrdered := by decide

def importedSymbol : GobjSymbol where
  name := symbolNominalName
  body := .imported 0

def importedSymbols : GobjSymbolTable where
  entries := Vec.singleton importedSymbol
  countFits := by decide
  namesUnique := by decide

example : importedSymbols.ValidForSections sections := by decide
example : importedSymbols.ValidForImports oneImport := by decide
example : oneImport.AllUsedBy importedSymbols := by decide
example : relocations.IndicesValid sections importedSymbols := by decide

def importedTables : GobjLinkedTables where
  sections := sections
  symbols := importedSymbols
  relocations := relocations
  imports := oneImport
  symbolExtentsValid := by decide
  symbolImportsValid := by decide
  allImportsUsed := by decide
  relocationIndicesValid := by decide
  relocationLocationsValid := by decide

theorem importedSymbolsFit :
    (writeGobjSymbolTable importedSymbols).length < 2 ^ 32 := by
  rw [length_writeGobjSymbolTable]
  decide

theorem oneImportFit :
    (writeGobjImportManifest oneImport).length < 2 ^ 32 := by
  unfold oneImport importedEntry symbolNominalName symbolName
    writeGobjImportManifest writeGobjImportEntryList
    writeGobjImportEntry writeGobjImportSubject writeGobjNominalId
  simp [Vec.singleton, writeByte, writeGobjImportEntryList]

example : parseGobjLinkedTables
    (payload.withLinkedTables importedTables sectionsFit importedSymbolsFit
      relocationsFit oneImportFit) = .ok importedTables := by
  exact parseGobjLinkedTables_withLinkedTables payload importedTables sectionsFit
    importedSymbolsFit relocationsFit oneImportFit

def wrongImportedSymbol : GobjSymbol :=
  { importedSymbol with name := ⟨⟨Vec.singleton 0x78, by decide⟩, symbolName⟩ }

def wrongImportedSymbols : GobjSymbolTable where
  entries := Vec.singleton wrongImportedSymbol
  countFits := by decide
  namesUnique := by decide

example : ¬ wrongImportedSymbols.ValidForImports oneImport := by decide

def missingImportSymbols : GobjSymbolTable where
  entries := Vec.singleton { importedSymbol with body := .imported 1 }
  countFits := by decide
  namesUnique := by decide

example : ¬ missingImportSymbols.ValidForImports oneImport := by decide
example : ¬ oneImport.AllUsedBy symbols := by decide

end Grass.Tests.Artifact.Binary.Gobj.LinkedTables
