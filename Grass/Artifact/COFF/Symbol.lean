import Grass.Artifact.COFF.Relocation

/-!
# Raw COFF symbol cells

COFF counts both primary symbols and auxiliary records in 18-byte cells.
`SymbolCell` preserves each cell losslessly, while `SymbolTable` couples the
total cell count to the file header. Interpreting names, signed section numbers,
storage classes, and auxiliary variants is a separate validation layer.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Lossless field partition of one 18-byte COFF symbol-table cell. For a
primary symbol these fields have their standard COFF meanings; an auxiliary
cell remains raw data split at the same byte boundaries. -/
structure SymbolCell where
  rawName : SizedByteArray 8
  value : BitVec 32
  sectionNumber : BitVec 16
  symbolType : BitVec 16
  storageClass : Byte
  numberOfAuxSymbols : Byte
deriving DecidableEq, Repr

/-- Product shape used by the generic sequencing grammar. -/
abbrev SymbolCellFields :=
  SizedByteArray 8 × BitVec 32 × BitVec 16 × BitVec 16 × Byte × Byte

/-- Forget labels without interpreting any symbol or auxiliary-cell fact. -/
def SymbolCell.toFields (cell : SymbolCell) : SymbolCellFields :=
  (cell.rawName, cell.value, cell.sectionNumber, cell.symbolType,
    cell.storageClass, cell.numberOfAuxSymbols)

/-- Restore the named lossless cell representation. -/
def SymbolCell.ofFields (fields : SymbolCellFields) : SymbolCell where
  rawName := fields.1
  value := fields.2.1
  sectionNumber := fields.2.2.1
  symbolType := fields.2.2.2.1
  storageClass := fields.2.2.2.2.1
  numberOfAuxSymbols := fields.2.2.2.2.2

/-- Symbol cells and their grammar products are a total isomorphism. -/
def symbolCellFieldsIsomorphism : Isomorphism SymbolCellFields SymbolCell where
  forward := SymbolCell.ofFields
  backward := SymbolCell.toFields
  backward_forward := by
    intro fields
    rcases fields with ⟨a, b, c, d, e, f⟩
    rfl
  forward_backward := by
    intro cell
    rcases cell with ⟨a, b, c, d, e, f⟩
    rfl

/-- Generic grammar for the six byte-level fields of a symbol cell. -/
def symbolCellFieldsFormat : Format SymbolCellFields :=
  .seq (fixedBytesFormat 8) fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq anyByteFormat fun _ =>
  anyByteFormat

/-- Typed language of one lossless 18-byte COFF symbol cell. -/
def symbolCellFormat : Format SymbolCell :=
  symbolCellFieldsFormat.iso symbolCellFieldsIsomorphism

/-- Decode one symbol cell after the 18-byte bound is established. -/
private def readCompleteSymbolCell
    (input : Std.Logical.ByteArray) : ParseResult SymbolCell :=
  match takeExactSized 8 input with
  | .done rawName rest =>
    match takeLittleEndian 4 rest with
    | .done value rest =>
      match takeLittleEndian 2 rest with
      | .done sectionNumber rest =>
        match takeLittleEndian 2 rest with
        | .done symbolType rest =>
          match takeByte rest with
          | .done storageClass rest =>
            match takeByte rest with
            | .done numberOfAuxSymbols rest => .done {
                rawName, value, sectionNumber, symbolType,
                storageClass, numberOfAuxSymbols } rest
            | .needMore hint => .needMore hint
            | .invalid error => .invalid error
          | .needMore hint => .needMore hint
          | .invalid error => .invalid error
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse one lossless symbol cell with exact whole-cell deficit reporting. -/
def readSymbolCell (input : Std.Logical.ByteArray) : ParseResult SymbolCell :=
  if 18 ≤ input.length then
    readCompleteSymbolCell input
  else
    .needMore (some (18 - input.length))

/-- A truncated symbol cell reports its exact missing byte count. -/
theorem readSymbolCell_short {input : Std.Logical.ByteArray}
    (short : input.length < 18) :
    readSymbolCell input = .needMore (some (18 - input.length)) := by
  simp [readSymbolCell, Nat.not_le.mpr short]

/-- Serialize a lossless symbol cell in canonical field order. -/
def writeSymbolCell (cell : SymbolCell) : Std.Logical.ByteArray :=
  writeExact cell.rawName ++
  writeLittleEndian (count := 4) cell.value ++
  writeLittleEndian (count := 2) cell.sectionNumber ++
  writeLittleEndian (count := 2) cell.symbolType ++
  writeByte cell.storageClass ++
  writeByte cell.numberOfAuxSymbols

/-- Canonical symbol cells occupy exactly 18 bytes. -/
@[simp] theorem length_writeSymbolCell (cell : SymbolCell) :
    (writeSymbolCell cell).length = 18 := by
  simp [writeSymbolCell, writeLittleEndian, isoWriter, writeExact, writeByte]

/-- Every canonical symbol-cell serialization derives from its typed grammar. -/
theorem writeSymbolCell_derives (cell : SymbolCell) :
    Derives symbolCellFormat (writeSymbolCell cell) cell Vec.empty := by
  rcases cell with ⟨name, value, sectionNumber, symbolType, storage, auxiliary⟩
  unfold symbolCellFormat
  refine @Derives.iso SymbolCellFields SymbolCell symbolCellFieldsFormat
    symbolCellFieldsIsomorphism _ Vec.empty
    (name, value, sectionNumber, symbolType, storage, auxiliary) ?_
  simp only [writeSymbolCell, Vec.append_assoc]
  unfold symbolCellFieldsFormat littleEndianU16Format littleEndianU32Format
  exact Derives.seqAppend
    ((writeExact_realizes 8).sound name)
    (Derives.seqAppend
      ((writeLittleEndian_realizes 4).sound value)
      (Derives.seqAppend
        ((writeLittleEndian_realizes 2).sound sectionNumber)
        (Derives.seqAppend
          ((writeLittleEndian_realizes 2).sound symbolType)
          (Derives.seqAppend
            (writeByte_realizes.sound storage)
            (writeByte_realizes.sound auxiliary)))))

/-- Canonical symbol-cell reading and writing preserve an arbitrary suffix. -/
@[simp] theorem readSymbolCell_writeSymbolCell_append
    (cell : SymbolCell) (rest : Std.Logical.ByteArray) :
    readSymbolCell (writeSymbolCell cell ++ rest) = .done cell rest := by
  rcases cell with ⟨name, value, sectionNumber, symbolType, storage, auxiliary⟩
  simp only [readSymbolCell, Vec.length_append, length_writeSymbolCell]
  have enough : 18 ≤ 18 + rest.length := by omega
  simp only [enough, ite_true]
  simp only [readCompleteSymbolCell, writeSymbolCell, Vec.append_assoc,
    takeExactSized_writeExact_append,
    takeLittleEndian_writeLittleEndian_append, takeByte_writeByte_append]

/-- Whole-cell canonical writer/reader round trip. -/
@[simp] theorem readSymbolCell_writeSymbolCell (cell : SymbolCell) :
    readSymbolCell (writeSymbolCell cell) = .done cell Vec.empty := by
  simpa using readSymbolCell_writeSymbolCell_append cell Vec.empty

/-! ## Header-count-coupled symbol tables -/

/-- Recursive serializer beneath the public symbol-table writer. -/
private def writeSymbolCellList : List SymbolCell → Std.Logical.ByteArray
  | [] => Vec.empty
  | cell :: rest => writeSymbolCell cell ++ writeSymbolCellList rest

/-- Serialize symbol and auxiliary cells in their table order. -/
def writeSymbolCells (cells : Vec SymbolCell) : Std.Logical.ByteArray :=
  writeSymbolCellList cells.toList

/-- Consing a cell emits it before the remaining table. -/
@[simp] theorem writeSymbolCells_cons (cell : SymbolCell)
    (rest : Vec SymbolCell) :
    writeSymbolCells (Vec.singleton cell ++ rest) =
      writeSymbolCell cell ++ writeSymbolCells rest := by
  rfl

/-- Symbol tables occupy exactly 18 bytes per counted cell. -/
@[simp] theorem length_writeSymbolCells (cells : Vec SymbolCell) :
    (writeSymbolCells cells).length = 18 * cells.length := by
  induction cells using Vec.recOnCons with
  | empty => rfl
  | cons cell rest ih =>
      rw [writeSymbolCells_cons, Vec.length_append, length_writeSymbolCell, ih]
      simp [Nat.mul_add]

/-- Parse exactly `count` ordered symbol-table cells. -/
def readSymbolCells :
    (count : Nat) → Std.Logical.ByteArray → ParseResult (Vec SymbolCell)
  | 0, input => .done Vec.empty input
  | count + 1, input =>
    match readSymbolCell input with
    | .done cell rest =>
      match readSymbolCells count rest with
      | .done cells suffix => .done (Vec.singleton cell ++ cells) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- Successful bounded symbol-table parsing returns the requested cell count. -/
theorem readSymbolCells_done_length {count : Nat} {input cells rest}
    (success : readSymbolCells count input = .done cells rest) :
    cells.length = count := by
  induction count generalizing input cells rest with
  | zero =>
      simp only [readSymbolCells] at success
      injection success with cellsEq
      rw [← cellsEq]
      simp
  | succ count ih =>
      simp only [readSymbolCells] at success
      split at success <;> try contradiction
      next cell suffix parsedCell =>
        split at success <;> try contradiction
        next tail final parsedTail =>
          injection success with cellsEq restEq
          rw [← cellsEq, Vec.length_append]
          simp only [Vec.length_singleton]
          rw [ih parsedTail]
          omega

/-- Bounded symbol-cell vectors round-trip with exact suffix preservation. -/
@[simp] theorem readSymbolCells_writeSymbolCells_append
    (cells : Vec SymbolCell) (rest : Std.Logical.ByteArray) :
    readSymbolCells cells.length (writeSymbolCells cells ++ rest) =
      .done cells rest := by
  induction cells using Vec.recOnCons generalizing rest with
  | empty =>
      change readSymbolCells 0 (Vec.empty ++ rest) = .done Vec.empty rest
      simp [readSymbolCells]
  | cons cell tail ih =>
      rw [writeSymbolCells_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add, Vec.append_assoc,
        readSymbolCells]
      rw [readSymbolCell_writeSymbolCell_append]
      simp only
      rw [ih rest]

/-- Every serialized cell vector derives from the matching repetition grammar. -/
theorem writeSymbolCells_derives (cells : Vec SymbolCell) :
    Derives (.repeat cells.length symbolCellFormat)
      (writeSymbolCells cells) cells Vec.empty := by
  induction cells using Vec.recOnCons with
  | empty => exact Derives.repeatZero symbolCellFormat Vec.empty
  | cons cell tail ih =>
      rw [writeSymbolCells_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add]
      exact Derives.repeatSucc
        ((writeSymbolCell_derives cell).appendSuffix (writeSymbolCells tail)) ih

/-- Proof-bearing symbol-cell vector for one particular file header. -/
abbrev CheckedSymbolTable (header : Header) :=
  {cells : Vec SymbolCell // cells.length = header.numberOfSymbols.toNat}

/-- Symbol and auxiliary cells whose total count is coupled to the file header. -/
structure SymbolTable (header : Header) where
  cells : Vec SymbolCell
  cellCount : cells.length = header.numberOfSymbols.toNat
deriving DecidableEq, Repr

/-- Convert a checked vector into the named symbol-table wrapper. -/
def SymbolTable.ofChecked {header : Header} (table : CheckedSymbolTable header) :
    SymbolTable header where
  cells := table.1
  cellCount := table.2

/-- Convert the named wrapper back to its count-checked vector. -/
def SymbolTable.toChecked {header : Header} (table : SymbolTable header) :
    CheckedSymbolTable header :=
  ⟨table.cells, table.cellCount⟩

/-- Named and subtype symbol-table representations are totally isomorphic. -/
def symbolTableIsomorphism (header : Header) :
    Isomorphism (CheckedSymbolTable header) (SymbolTable header) where
  forward := SymbolTable.ofChecked
  backward := SymbolTable.toChecked
  backward_forward := by intro table; rcases table with ⟨cells, count⟩; rfl
  forward_backward := by intro table; rcases table with ⟨cells, count⟩; rfl

/-- Count-refined grammar for the cells declared by one file header. -/
def checkedSymbolTableFormat (header : Header) :
    Format (CheckedSymbolTable header) :=
  (Format.repeat header.numberOfSymbols.toNat symbolCellFormat).refineValue
    fun cells => cells.length = header.numberOfSymbols.toNat

/-- Typed raw symbol-table language coupled to its file header. -/
def symbolTableFormat (header : Header) : Format (SymbolTable header) :=
  (checkedSymbolTableFormat header).iso (symbolTableIsomorphism header)

/-- Parse the complete header-declared symbol table after preflighting its
entire 18-byte-per-cell extent. -/
def readSymbolTable (header : Header) (input : Std.Logical.ByteArray) :
    ParseResult (SymbolTable header) :=
  let required := 18 * header.numberOfSymbols.toNat
  if required ≤ input.length then
    match readSymbolCells header.numberOfSymbols.toNat input with
    | .done cells rest =>
      if count : cells.length = header.numberOfSymbols.toNat then
        .done { cells, cellCount := count } rest
      else
        .invalid (.malformed "symbol-table cell count mismatch")
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else
    .needMore (some (required - input.length))

/-- A short symbol table reports its exact whole-table deficit. -/
theorem readSymbolTable_short (header : Header) {input : Std.Logical.ByteArray}
    (short : input.length < 18 * header.numberOfSymbols.toNat) :
    readSymbolTable header input =
      .needMore (some (18 * header.numberOfSymbols.toNat - input.length)) := by
  simp [readSymbolTable, Nat.not_le.mpr short]

/-- Serialize every counted cell in a header-coupled symbol table. -/
def writeSymbolTable {header : Header}
    (table : SymbolTable header) : Std.Logical.ByteArray :=
  writeSymbolCells table.cells

/-- Serialized symbol-table size is exactly 18 bytes times the header count. -/
@[simp] theorem length_writeSymbolTable {header : Header}
    (table : SymbolTable header) :
    (writeSymbolTable table).length = 18 * header.numberOfSymbols.toNat := by
  simp [writeSymbolTable, table.cellCount]

/-- Header-coupled symbol tables round-trip with exact suffix preservation. -/
@[simp] theorem readSymbolTable_writeSymbolTable_append {header : Header}
    (table : SymbolTable header) (rest : Std.Logical.ByteArray) :
    readSymbolTable header (writeSymbolTable table ++ rest) = .done table rest := by
  rcases table with ⟨cells, count⟩
  simp only [readSymbolTable, writeSymbolTable, Vec.length_append,
    length_writeSymbolCells]
  have enough : 18 * header.numberOfSymbols.toNat ≤
      18 * cells.length + rest.length := by simp [count]
  simp only [enough, ite_true]
  have parsed : readSymbolCells header.numberOfSymbols.toNat
      (writeSymbolCells cells ++ rest) = .done cells rest := by
    simpa only [← count] using
      readSymbolCells_writeSymbolCells_append cells rest
  rw [parsed]
  simp only [count, ↓reduceDIte]

/-- Whole-table canonical round trip. -/
@[simp] theorem readSymbolTable_writeSymbolTable {header : Header}
    (table : SymbolTable header) :
    readSymbolTable header (writeSymbolTable table) = .done table Vec.empty := by
  simpa using readSymbolTable_writeSymbolTable_append table Vec.empty

/-- Every symbol-table serialization derives from its count-refined grammar. -/
theorem writeSymbolTable_derives {header : Header} (table : SymbolTable header) :
    Derives (symbolTableFormat header) (writeSymbolTable table) table Vec.empty := by
  rcases table with ⟨cells, count⟩
  unfold symbolTableFormat
  refine @Derives.iso (CheckedSymbolTable header) (SymbolTable header)
    (checkedSymbolTableFormat header) (symbolTableIsomorphism header)
    _ Vec.empty ⟨cells, count⟩ ?_
  unfold checkedSymbolTableFormat
  apply Derives.lift
  simpa only [writeSymbolTable, count] using writeSymbolCells_derives cells

end Grass.Artifact.COFF
