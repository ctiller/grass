import Grass.Artifact.Binary.Gobj.Relocation

/-! # Typed `.gobj` relocation fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Relocation

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical

def entry : GobjRelocation where
  sectionIndex := 1
  offset := 0x1020
  targetSymbolIndex := 1
  kind := 4
  addend := 7

def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa, 0xbb]

example : (writeGobjRelocation entry).length = 28 := by
  rw [length_writeGobjRelocation]

example : readGobjRelocation (writeGobjRelocation entry ++ suffix) =
    .done entry suffix := by
  exact readGobjRelocation_write_append entry suffix

example : entry.IndicesValid 2 2 := by decide
example : ¬ entry.IndicesValid 1 2 := by decide
example : ¬ entry.IndicesValid 2 1 := by decide

def table : GobjRelocationTable := ⟨Vec.singleton entry, by decide⟩

example : (writeGobjRelocationTable table).length = 32 := by
  rw [length_writeGobjRelocationTable]
  decide

example : readGobjRelocationTable
    (writeGobjRelocationTable table ++ suffix) = .done table suffix := by
  exact readGobjRelocationTable_write_append table suffix

example : readGobjRelocationTable (Vec.fromList [2, 0, 0, 0]) =
    .needMore (some 56) := by rfl

def sectionName : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x2e, 0x74], by decide⟩

def emptyBody : U32LengthPrefixedBytes := ⟨Vec.empty, by decide⟩

def sectionEntry : GobjSection where
  name := sectionName
  alignment := ⟨0, by decide⟩
  permissions := ⟨1, by decide⟩
  contents := emptyBody

def sections : GobjSectionTable :=
  ⟨Vec.fromList [sectionEntry, sectionEntry], by decide⟩

def symbolName : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x73], by decide⟩

def symbolNominalName : GobjNominalId := ⟨emptyBody, symbolName⟩

def symbolEntry (offset : BitVec 64) : GobjSymbol where
  name := symbolNominalName
  body := .defined {
    binding := .local
    sectionIndex := 0
    offset := offset
    size := 0
    extentFits := by
      simpa using Nat.le_of_lt (BitVec.isLt offset) }

def symbols : GobjSymbolTable where
  entries := Vec.fromList [symbolEntry 0, { symbolEntry 1 with
    name := ⟨emptyBody, ⟨Vec.fromList [0x74], by decide⟩⟩ }]
  countFits := by decide
  namesUnique := by decide

example : table.IndicesValid sections symbols := by decide

def badTable : GobjRelocationTable :=
  ⟨Vec.singleton { entry with targetSymbolIndex := 3 }, by decide⟩

example : ¬ badTable.IndicesValid sections symbols := by decide

def boundedContents : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x90, 0x90, 0xc3], by decide⟩

def profileOwner : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x67], by decide⟩

def profileA : GobjRelocationProfileId where
  owner := profileOwner
  name := symbolName
  version := 1

def profileB : GobjRelocationProfileId where
  owner := profileOwner
  name := sectionName
  version := 1

def boundedSection : GobjSection where
  name := sectionName
  alignment := ⟨0, by decide⟩
  permissions := ⟨1, by decide⟩
  profile := .relocatable profileA
  contents := boundedContents

def boundedSections : GobjSectionTable :=
  ⟨Vec.singleton boundedSection, by decide⟩

def emptySections : GobjSectionTable :=
  ⟨Vec.singleton { boundedSection with contents := emptyBody }, by decide⟩

def boundedEntry (offset : BitVec 64) : GobjRelocation :=
  { entry with sectionIndex := 0, targetSymbolIndex := 0, offset := offset }

def widthOne : RelocationKindInterpretation :=
  .singleKind profileA 4 1 (by decide)

def widthTwo : RelocationKindInterpretation :=
  .singleKind profileB 4 2 (by decide)

def registry : RelocationProfileRegistry where
  resolve profile :=
    if profile = profileA then some widthOne
    else if profile = profileB then some widthTwo
    else none

/-- An empty selected section has no valid relocation start. -/
example : ¬ (boundedEntry 0).ValidFor registry emptySections symbols := by decide

/-- The first byte beyond the section is not a relocation start. -/
example : ¬ (boundedEntry 3).ValidFor registry boundedSections symbols := by decide

/-- Conversion to `Nat` prevents a maximal fixed-width offset from wrapping. -/
example : ¬ (boundedEntry 18446744073709551615).ValidFor
    registry boundedSections symbols := by decide

/-- A one-byte patch may start at the final byte. -/
example : (boundedEntry 2).ValidFor registry boundedSections symbols := by decide

/-- A multi-byte patch beginning at the final byte crosses the section end. -/
def profileBSections : GobjSectionTable :=
  ⟨Vec.singleton { boundedSection with profile := .relocatable profileB },
    by decide⟩

example : ¬ (boundedEntry 2).ValidFor registry profileBSections symbols := by decide

def profileC : GobjRelocationProfileId where
  owner := profileOwner
  name := symbolName
  version := 2

def unknownProfileSections : GobjSectionTable :=
  ⟨Vec.singleton { boundedSection with profile := .relocatable profileC },
    by decide⟩

example : ¬ (boundedEntry 0).ValidFor registry unknownProfileSections symbols :=
  by decide

example : ¬ { boundedEntry 0 with kind := 99 }.ValidFor
    registry boundedSections symbols := by decide

def noRelocationSections : GobjSectionTable :=
  ⟨Vec.singleton { boundedSection with profile := .noRelocations }, by decide⟩

example : ¬ (boundedEntry 0).ValidFor registry noRelocationSections symbols :=
  by decide

def heterogeneousSections : GobjSectionTable :=
  ⟨Vec.fromList [boundedSection,
    { boundedSection with profile := .relocatable profileB }], by decide⟩

def heterogeneousRelocations : GobjRelocationTable :=
  ⟨Vec.fromList [boundedEntry 2,
    { boundedEntry 1 with sectionIndex := 1 }], by decide⟩

example : heterogeneousRelocations.ValidFor registry heterogeneousSections
    symbols := by decide

example : (resolveGobjRelocationTable registry boundedSections symbols
    ⟨Vec.singleton (boundedEntry 2), by decide⟩).isOk := by decide

example : resolveGobjRelocationTable registry profileBSections symbols
    ⟨Vec.singleton (boundedEntry 2), by decide⟩ =
      .error (.malformed
        ".gobj relocation patch is out of bounds or unknown") := by rfl

theorem table_lengthFits :
    (writeGobjRelocationTable table).length < 2 ^ 32 := by
  rw [length_writeGobjRelocationTable]
  decide

def framedTable : U32LengthPrefixedBytes := table.toFramed table_lengthFits

example : parseGobjRelocationTableBody framedTable = .ok table := by
  exact parseGobjRelocationTableBody_toFramed table table_lengthFits

def trailingTableBody : U32LengthPrefixedBytes :=
  ⟨writeGobjRelocationTable table ++ Vec.singleton 0xff, by
    rw [Vec.length_append, length_writeGobjRelocationTable]
    decide⟩

example : parseGobjRelocationTableBody trailingTableBody =
    .error .trailingInput := by
  unfold parseGobjRelocationTableBody trailingTableBody
  rw [readGobjRelocationTable_write_append]
  rfl

def truncatedTableBody : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [1, 0, 0, 0], by decide⟩

example : parseGobjRelocationTableBody truncatedTableBody =
    .error (.malformed "truncated .gobj relocation-table body") := by rfl

end Grass.Tests.Artifact.Binary.Gobj.Relocation
