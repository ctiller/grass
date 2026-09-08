import Grass.Artifact.COFF.StringTable

/-!
# Contextual COFF symbol validation

This module connects typed primary symbols to one exact parsed string table and
checks auxiliary-cell skip counts over lossless raw symbol tables. It does not
interpret storage classes or auxiliary payload variants.
-/

namespace Grass.Artifact.COFF

open Grass.Grammar Grass.Std.Logical

/-! ## Names validated against one string table -/

/-- A primary symbol whose name is valid in one particular string table. -/
structure ValidatedSymbol (strings : StringTable) where
  symbol : Symbol
  nameValid : symbol.name.ValidIn strings
deriving DecidableEq, Repr

/-- Subtype representation used by grammar refinement. -/
abbrev CheckedSymbol (strings : StringTable) :=
  {symbol : Symbol // symbol.name.ValidIn strings}

/-- Restore the named validated-symbol wrapper. -/
def ValidatedSymbol.ofChecked {strings : StringTable}
    (symbol : CheckedSymbol strings) : ValidatedSymbol strings where
  symbol := symbol.1
  nameValid := symbol.2

/-- Forget only the wrapper label, retaining name validity. -/
def ValidatedSymbol.toChecked {strings : StringTable}
    (symbol : ValidatedSymbol strings) : CheckedSymbol strings :=
  ⟨symbol.symbol, symbol.nameValid⟩

/-- Named and subtype validated-symbol representations are totally isomorphic. -/
def validatedSymbolIsomorphism (strings : StringTable) :
    Isomorphism (CheckedSymbol strings) (ValidatedSymbol strings) where
  forward := ValidatedSymbol.ofChecked
  backward := ValidatedSymbol.toChecked
  backward_forward := by intro symbol; rcases symbol with ⟨value, valid⟩; rfl
  forward_backward := by intro symbol; rcases symbol with ⟨value, valid⟩; rfl

/-- Name-refined grammar for a primary symbol in one string-table context. -/
def checkedSymbolFormat (strings : StringTable) : Format (CheckedSymbol strings) :=
  symbolFormat.refineValue fun symbol => symbol.name.ValidIn strings

/-- Typed grammar of a primary symbol validated against one string table. -/
def validatedSymbolFormat (strings : StringTable) :
    Format (ValidatedSymbol strings) :=
  (checkedSymbolFormat strings).iso (validatedSymbolIsomorphism strings)

/-- Parse a primary symbol and reject a long-name offset that is not valid in
the supplied parsed string table. -/
def readValidatedSymbol (strings : StringTable)
    (input : Std.Logical.ByteArray) : ParseResult (ValidatedSymbol strings) :=
  match readSymbol input with
  | .done symbol rest =>
    if valid : symbol.name.ValidIn strings then
      .done { symbol, nameValid := valid } rest
    else
      .invalid (.malformed "COFF symbol name is invalid in its string table")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Serialize the already-validated primary symbol. -/
def writeValidatedSymbol {strings : StringTable}
    (symbol : ValidatedSymbol strings) : Std.Logical.ByteArray :=
  writeSymbol symbol.symbol

/-- Validated primary symbols retain the fixed 18-byte width. -/
@[simp] theorem length_writeValidatedSymbol {strings : StringTable}
    (symbol : ValidatedSymbol strings) :
    (writeValidatedSymbol symbol).length = 18 := by
  simp [writeValidatedSymbol]

/-- `readValidatedSymbol_writeValidatedSymbol_append` states that a validated
symbol round-trips in its exact string-table context and preserves its suffix. -/
@[simp] theorem readValidatedSymbol_writeValidatedSymbol_append
    {strings : StringTable} (symbol : ValidatedSymbol strings)
    (rest : Std.Logical.ByteArray) :
    readValidatedSymbol strings (writeValidatedSymbol symbol ++ rest) =
      .done symbol rest := by
  rcases symbol with ⟨symbol, valid⟩
  unfold readValidatedSymbol writeValidatedSymbol
  rw [readSymbol_writeSymbol_append]
  simp only [valid, dite_true]

/-- Every validated-symbol serialization derives from its refined grammar. -/
theorem writeValidatedSymbol_derives {strings : StringTable}
    (symbol : ValidatedSymbol strings) :
    Derives (validatedSymbolFormat strings) (writeValidatedSymbol symbol)
      symbol Vec.empty := by
  rcases symbol with ⟨value, valid⟩
  unfold validatedSymbolFormat
  refine @Derives.iso (CheckedSymbol strings) (ValidatedSymbol strings)
    (checkedSymbolFormat strings) (validatedSymbolIsomorphism strings)
    _ Vec.empty ⟨value, valid⟩ ?_
  unfold checkedSymbolFormat
  apply Derives.lift
  exact writeSymbol_derives value

/-! ## Auxiliary-cell layout validation -/

/-- Bounded auxiliary-layout scanner. Each primary cell consumes itself and
skips its declared number of following auxiliary cells; `fuel` bounds even a
zero-auxiliary scan independently of list recursion details. -/
def validAuxLayoutScan : Nat → List SymbolCell → Bool
  | 0, cells => cells.isEmpty
  | _ + 1, [] => true
  | fuel + 1, cell :: rest =>
    let auxiliaryCount := cell.numberOfAuxSymbols.toNat
    if auxiliaryCount ≤ rest.length then
      validAuxLayoutScan fuel (rest.drop auxiliaryCount)
    else
      false

/-- Whether raw symbol cells partition exactly into primary cells followed by
their declared auxiliary-cell runs. -/
def SymbolTable.AuxLayoutValid {header : Header}
    (table : SymbolTable header) : Prop :=
  validAuxLayoutScan table.cells.length table.cells.toList = true

instance {header : Header} (table : SymbolTable header) :
    Decidable table.AuxLayoutValid := by
  unfold SymbolTable.AuxLayoutValid
  infer_instance

/-- A header-coupled raw symbol table with a validated auxiliary-cell layout. -/
structure AuxValidatedSymbolTable (header : Header) where
  table : SymbolTable header
  auxLayoutValid : table.AuxLayoutValid
deriving DecidableEq, Repr

/-- Subtype representation used by auxiliary-layout grammar refinement. -/
abbrev CheckedAuxSymbolTable (header : Header) :=
  {table : SymbolTable header // table.AuxLayoutValid}

/-- Convert a checked raw table into the named validated wrapper. -/
def AuxValidatedSymbolTable.ofChecked {header : Header}
    (table : CheckedAuxSymbolTable header) : AuxValidatedSymbolTable header where
  table := table.1
  auxLayoutValid := table.2

/-- Forget only the wrapper label, retaining auxiliary-layout validity. -/
def AuxValidatedSymbolTable.toChecked {header : Header}
    (table : AuxValidatedSymbolTable header) : CheckedAuxSymbolTable header :=
  ⟨table.table, table.auxLayoutValid⟩

/-- Named and subtype auxiliary-validated tables are totally isomorphic. -/
def auxValidatedSymbolTableIsomorphism (header : Header) :
    Isomorphism (CheckedAuxSymbolTable header)
      (AuxValidatedSymbolTable header) where
  forward := AuxValidatedSymbolTable.ofChecked
  backward := AuxValidatedSymbolTable.toChecked
  backward_forward := by intro table; rcases table with ⟨value, valid⟩; rfl
  forward_backward := by intro table; rcases table with ⟨value, valid⟩; rfl

/-- Auxiliary-layout refinement of a header-count-coupled raw symbol table. -/
def checkedAuxSymbolTableFormat (header : Header) :
    Format (CheckedAuxSymbolTable header) :=
  (symbolTableFormat header).refineValue SymbolTable.AuxLayoutValid

/-- Typed grammar of a symbol table with valid auxiliary-cell runs. -/
def auxValidatedSymbolTableFormat (header : Header) :
    Format (AuxValidatedSymbolTable header) :=
  (checkedAuxSymbolTableFormat header).iso
    (auxValidatedSymbolTableIsomorphism header)

/-- Parse a count-coupled symbol table and reject inconsistent auxiliary runs. -/
def readAuxValidatedSymbolTable (header : Header)
    (input : Std.Logical.ByteArray) :
    ParseResult (AuxValidatedSymbolTable header) :=
  match readSymbolTable header input with
  | .done table rest =>
    if valid : table.AuxLayoutValid then
      .done { table, auxLayoutValid := valid } rest
    else
      .invalid (.malformed "COFF auxiliary symbol layout is inconsistent")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Serialize the underlying count-coupled symbol table. -/
def writeAuxValidatedSymbolTable {header : Header}
    (table : AuxValidatedSymbolTable header) : Std.Logical.ByteArray :=
  writeSymbolTable table.table

/-- Auxiliary-validated tables preserve their header-count-derived size. -/
@[simp] theorem length_writeAuxValidatedSymbolTable {header : Header}
    (table : AuxValidatedSymbolTable header) :
    (writeAuxValidatedSymbolTable table).length =
      18 * header.numberOfSymbols.toNat := by
  simp [writeAuxValidatedSymbolTable]

/-- Auxiliary-validated symbol tables round-trip with exact suffix preservation. -/
@[simp] theorem readAuxValidatedSymbolTable_write_append {header : Header}
    (table : AuxValidatedSymbolTable header)
    (rest : Std.Logical.ByteArray) :
    readAuxValidatedSymbolTable header
      (writeAuxValidatedSymbolTable table ++ rest) = .done table rest := by
  rcases table with ⟨table, valid⟩
  unfold readAuxValidatedSymbolTable writeAuxValidatedSymbolTable
  rw [readSymbolTable_writeSymbolTable_append]
  simp only [valid, dite_true]

/-- Every auxiliary-validated table serialization derives from its refined
grammar. -/
theorem writeAuxValidatedSymbolTable_derives {header : Header}
    (table : AuxValidatedSymbolTable header) :
    Derives (auxValidatedSymbolTableFormat header)
      (writeAuxValidatedSymbolTable table) table Vec.empty := by
  rcases table with ⟨value, valid⟩
  unfold auxValidatedSymbolTableFormat
  refine @Derives.iso (CheckedAuxSymbolTable header)
    (AuxValidatedSymbolTable header) (checkedAuxSymbolTableFormat header)
    (auxValidatedSymbolTableIsomorphism header) _ Vec.empty
    ⟨value, valid⟩ ?_
  unfold checkedAuxSymbolTableFormat
  apply Derives.lift
  exact writeSymbolTable_derives value

end Grass.Artifact.COFF
