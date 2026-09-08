import Grass.Artifact.Binary.Gobj.LinkedTables

/-! # Cross-table `.gobj` validation fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.LinkedTables

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical

def sectionName : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x2e, 0x74], by decide⟩

def sectionContents : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x90, 0x90, 0xc3], by decide⟩

def sectionEntry : GobjSection where
  name := sectionName
  alignment := ⟨0, by decide⟩
  permissions := ⟨5, by decide⟩
  contents := sectionContents

def sections : GobjSectionTable := ⟨Vec.singleton sectionEntry, by decide⟩

def symbolName : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x66], by decide⟩

def symbolEntry : GobjSymbol where
  name := symbolName
  binding := .exported
  sectionIndex := 0
  offset := 1
  size := 2
  extentFits := by decide

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

def tables : GobjLinkedTables where
  sections := sections
  symbols := symbols
  relocations := relocations
  symbolExtentsValid := by decide
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

example : parseGobjLinkedTables
    (payload.withLinkedTables tables sectionsFit symbolsFit relocationsFit) =
      .ok tables := by
  exact parseGobjLinkedTables_withLinkedTables payload tables sectionsFit
    symbolsFit relocationsFit

def outOfBoundsSymbol : GobjSymbol :=
  { symbolEntry with offset := 2, size := 2, extentFits := by decide }

def badSymbols : GobjSymbolTable where
  entries := Vec.singleton outOfBoundsSymbol
  countFits := by decide
  namesUnique := by decide

example : ¬ badSymbols.ValidForSections sections := by decide

def missingSectionSymbol : GobjSymbol :=
  { symbolEntry with sectionIndex := 1 }

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

end Grass.Tests.Artifact.Binary.Gobj.LinkedTables
