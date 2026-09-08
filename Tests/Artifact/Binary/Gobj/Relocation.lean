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

def symbolEntry (offset : BitVec 64) : GobjSymbol where
  name := symbolName
  binding := .local
  sectionIndex := 0
  offset := offset
  size := 0
  extentFits := by
    simpa using Nat.le_of_lt (BitVec.isLt offset)

def symbols : GobjSymbolTable where
  entries := Vec.fromList [symbolEntry 0, { symbolEntry 1 with
    name := ⟨Vec.fromList [0x74], by decide⟩ }]
  countFits := by decide
  namesUnique := by decide

example : table.IndicesValid sections symbols := by decide

def badTable : GobjRelocationTable :=
  ⟨Vec.singleton { entry with targetSymbolIndex := 3 }, by decide⟩

example : ¬ badTable.IndicesValid sections symbols := by decide

def boundedContents : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [0x90, 0x90, 0xc3], by decide⟩

def boundedSection : GobjSection :=
  { sectionEntry with contents := boundedContents }

def boundedSections : GobjSectionTable :=
  ⟨Vec.singleton boundedSection, by decide⟩

def emptySections : GobjSectionTable :=
  ⟨Vec.singleton sectionEntry, by decide⟩

def boundedEntry (offset : BitVec 64) : GobjRelocation :=
  { entry with sectionIndex := 0, targetSymbolIndex := 0, offset := offset }

def widthOne : RelocationKindInterpretation :=
  .constant 1 (by decide)

def widthTwo : RelocationKindInterpretation :=
  .constant 2 (by decide)

/-- An empty selected section has no valid relocation start. -/
example : ¬ (boundedEntry 0).ValidFor widthOne emptySections symbols := by decide

/-- The first byte beyond the section is not a relocation start. -/
example : ¬ (boundedEntry 3).ValidFor widthOne boundedSections symbols := by decide

/-- Conversion to `Nat` prevents a maximal fixed-width offset from wrapping. -/
example : ¬ (boundedEntry 18446744073709551615).ValidFor
    widthOne boundedSections symbols := by decide

/-- A one-byte patch may start at the final byte. -/
example : (boundedEntry 2).ValidFor widthOne boundedSections symbols := by decide

/-- A multi-byte patch beginning at the final byte crosses the section end. -/
example : ¬ (boundedEntry 2).ValidFor widthTwo boundedSections symbols := by decide

example : (resolveGobjRelocationTable widthOne boundedSections symbols
    ⟨Vec.singleton (boundedEntry 2), by decide⟩).isOk := by decide

example : resolveGobjRelocationTable widthTwo boundedSections symbols
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
