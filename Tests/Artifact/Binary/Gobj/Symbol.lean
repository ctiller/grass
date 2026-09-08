import Grass.Artifact.Binary.Gobj.Symbol

/-! # Typed `.gobj` symbol fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Symbol

open Grass.Artifact.Binary Grass.Artifact.Binary.Gobj Grass.Grammar
  Grass.Std.Logical

def nameBytes : Std.Logical.ByteArray := Vec.fromList [0x6d, 0x61, 0x69, 0x6e]
def name : U32LengthPrefixedBytes := ⟨nameBytes, by decide⟩

def entry : GobjSymbol where
  name := name
  binding := .exported
  sectionIndex := 2
  offset := 16
  size := 32
  extentFits := by decide

def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa, 0xbb]

example : (writeGobjSymbol entry).length = 32 := by
  rw [length_writeGobjSymbol]
  decide

example : readGobjSymbol (writeGobjSymbol entry ++ suffix) =
    .done entry suffix := by
  exact readGobjSymbol_write_append entry suffix

example : readGobjSymbol (Vec.fromList [0, 0, 0, 0, 2]) =
    .invalid (.malformed "invalid .gobj symbol binding") := by rfl

example : readGobjSymbol (Vec.fromList [0, 0, 0, 0, 0, 1, 0, 0]) =
    .invalid (.malformed "nonzero .gobj symbol reserved field") := by rfl

def overflowBytes : Std.Logical.ByteArray :=
  Vec.fromList ([0, 0, 0, 0, 0, 0, 0, 0] ++
    [0, 0, 0, 0] ++
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] ++
    [2, 0, 0, 0, 0, 0, 0, 0])

example : readGobjSymbol overflowBytes =
    .invalid (.malformed ".gobj symbol extent overflows 64 bits") := by rfl

def table : GobjSymbolTable where
  entries := Vec.singleton entry
  countFits := by decide
  namesUnique := by decide

example : (writeGobjSymbolTable table).length = 36 := by
  rw [length_writeGobjSymbolTable]
  decide

example : readGobjSymbolTable (writeGobjSymbolTable table ++ suffix) =
    .done table suffix := by
  exact readGobjSymbolTable_write_append table suffix

example : readGobjSymbolTable (Vec.fromList [2, 0, 0, 0]) =
    .needMore (some 56) := by rfl

def duplicateBytes : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (2 : BitVec 32) ++
    writeGobjSymbol entry ++ writeGobjSymbol entry

example : readGobjSymbolTable duplicateBytes =
    .invalid (.malformed "duplicate .gobj symbol name") := by
  unfold duplicateBytes
  unfold readGobjSymbolTable
  simp only [Vec.append_assoc]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  rw [dif_pos (by decide : 28 * (2 : BitVec 32).toNat ≤
    (writeGobjSymbol entry ++ writeGobjSymbol entry).length)]
  have countEq : (2 : BitVec 32).toNat = 2 := by decide
  simp only [countEq, readGobjSymbolList]
  rw [readGobjSymbol_write_append]
  simp only
  rw [readGobjSymbol_write]
  simp only
  rw [dif_pos (by decide : [entry, entry].length = 2)]
  rw [dif_neg (by simp : ¬ ([entry, entry].map
    fun entry => entry.name.bytes).Nodup)]

theorem table_lengthFits : (writeGobjSymbolTable table).length < 2 ^ 32 := by
  rw [length_writeGobjSymbolTable]
  decide

def framedTable : U32LengthPrefixedBytes := table.toFramed table_lengthFits

example : parseGobjSymbolTableBody framedTable = .ok table := by
  exact parseGobjSymbolTableBody_toFramed table table_lengthFits

def trailingTableBytes : Std.Logical.ByteArray :=
  writeGobjSymbolTable table ++ Vec.singleton 0xff

def trailingTableBody : U32LengthPrefixedBytes :=
  ⟨trailingTableBytes, by
    unfold trailingTableBytes
    rw [Vec.length_append, length_writeGobjSymbolTable]
    decide⟩

example : parseGobjSymbolTableBody trailingTableBody =
    .error .trailingInput := by
  unfold parseGobjSymbolTableBody trailingTableBody trailingTableBytes
  rw [readGobjSymbolTable_write_append]
  rfl

def truncatedTableBody : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [1, 0, 0, 0], by decide⟩

example : parseGobjSymbolTableBody truncatedTableBody =
    .error (.malformed "truncated .gobj symbol-table body") := by rfl

end Grass.Tests.Artifact.Binary.Gobj.Symbol
