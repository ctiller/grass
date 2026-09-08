import Grass.Artifact.Binary.Gobj.ValidatedPayload

/-! # Structurally validated `.gobj` fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.ValidatedPayload

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical

def sectionName : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x2e, 0x74], by decide⟩

def sectionContents : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x90, 0xc3], by decide⟩

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

def symbolEntry : GobjSymbol where
  name := symbolName
  binding := .exported
  sectionIndex := 0
  offset := 0
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
  kind := 1
  addend := 0

def relocations : GobjRelocationTable :=
  ⟨Vec.singleton relocationEntry, by decide⟩

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

def validated : StructurallyValidGobj :=
  tables.toStructurallyValid payload sectionsFit symbolsFit relocationsFit

example : parseStructurallyValidGobj (writeGobj validated.payload) =
    .ok validated := by
  exact parseStructurallyValidGobj_write tables payload sectionsFit symbolsFit
    relocationsFit

example : parseStructurallyValidGobj (writeGobj validated.payload ++
    Vec.singleton 0xff) = .error .trailingInput := by
  unfold parseStructurallyValidGobj
  unfold validated GobjLinkedTables.toStructurallyValid
  unfold parseGobj
  rw [readGobj_write_append]
  rfl

example {input : Std.Logical.ByteArray} {parsed : StructurallyValidGobj}
    (success : parseStructurallyValidGobj input = .ok parsed) :
    parseGobj input = .ok parsed.payload := by
  exact parseStructurallyValidGobj_payloadExact success

end Grass.Tests.Artifact.Binary.Gobj.ValidatedPayload
