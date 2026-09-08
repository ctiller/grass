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

example : entry.ValidFor 2 2 := by decide
example : ¬ entry.ValidFor 1 2 := by decide
example : ¬ entry.ValidFor 2 1 := by decide

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

example : table.ValidFor sections symbols := by decide

def badTable : GobjRelocationTable :=
  ⟨Vec.singleton { entry with targetSymbolIndex := 3 }, by decide⟩

example : ¬ badTable.ValidFor sections symbols := by decide

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
