import Grass.Artifact.COFF.SymbolValidation
import Tests.Artifact.COFF.StringTable
import Tests.Artifact.COFF.SymbolName
import Tests.Artifact.COFF.Symbol

/-! # Contextual COFF symbol-validation fixtures -/

namespace Grass.Tests.Artifact.COFF.SymbolValidation

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.COFF.StringTable
open Grass.Tests.Artifact.COFF.SymbolName
open Grass.Tests.Artifact.COFF.Symbol

def longSymbol : Symbol := { typedMain with name := .stringTableOffset 4 }

def validatedLongSymbol : ValidatedSymbol longNames where
  symbol := longSymbol
  nameValid := by decide

example : readValidatedSymbol longNames
    (writeValidatedSymbol validatedLongSymbol ++ Vec.fromList [0xaa]) =
    .done validatedLongSymbol (Vec.fromList [0xaa]) := by
  exact readValidatedSymbol_writeValidatedSymbol_append validatedLongSymbol _

def invalidLongSymbol : Symbol := { typedMain with name := .stringTableOffset 9 }

example : readValidatedSymbol longNames (writeSymbol invalidLongSymbol) =
    .invalid (.malformed "COFF symbol name is invalid in its string table") := by
  rfl

def auxPrimary : SymbolCell := { mainCell with numberOfAuxSymbols := 1 }

def auxCell : SymbolCell := { mainCell with rawName := mainName, value := 0 }

def auxHeader : Header := { symbolHeader with numberOfSymbols := 2 }

def validAuxRawTable : SymbolTable auxHeader where
  cells := Vec.fromList [auxPrimary, auxCell]
  cellCount := by rfl

example : validAuxRawTable.AuxLayoutValid := by decide

def validAuxTable : AuxValidatedSymbolTable auxHeader where
  table := validAuxRawTable
  auxLayoutValid := by decide

example : readAuxValidatedSymbolTable auxHeader
    (writeAuxValidatedSymbolTable validAuxTable ++ Vec.fromList [0xbb]) =
    .done validAuxTable (Vec.fromList [0xbb]) := by
  exact readAuxValidatedSymbolTable_write_append validAuxTable _

def invalidAuxRawTable : SymbolTable auxHeader where
  cells := Vec.fromList [{ auxPrimary with numberOfAuxSymbols := 2 }, auxCell]
  cellCount := by rfl

example : ¬invalidAuxRawTable.AuxLayoutValid := by decide

example : Derives (auxValidatedSymbolTableFormat auxHeader)
    (writeAuxValidatedSymbolTable validAuxTable) validAuxTable Vec.empty := by
  exact writeAuxValidatedSymbolTable_derives validAuxTable

end Grass.Tests.Artifact.COFF.SymbolValidation
