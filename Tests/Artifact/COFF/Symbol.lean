import Grass.Artifact.COFF.Symbol
import Tests.Artifact.COFF.Header

/-! # Raw COFF symbol-cell and table fixtures -/

namespace Grass.Tests.Artifact.COFF.Symbol

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.COFF.Header

def mainName : SizedByteArray 8 :=
  ⟨Vec.fromList [0x6d, 0x61, 0x69, 0x6e, 0x00, 0x00, 0x00, 0x00], by decide⟩

def mainCell : SymbolCell where
  rawName := mainName
  value := 0x10
  sectionNumber := 1
  symbolType := 0x20
  storageClass := 2
  numberOfAuxSymbols := 0

def encodedMainCell : Std.Logical.ByteArray := Vec.fromList [
  0x6d, 0x61, 0x69, 0x6e, 0x00, 0x00, 0x00, 0x00,
  0x10, 0x00, 0x00, 0x00, 0x01, 0x00, 0x20, 0x00, 0x02, 0x00]

example : writeSymbolCell mainCell = encodedMainCell := by decide

example : readSymbolCell encodedMainCell = .done mainCell Vec.empty := by rfl

example : readSymbolCell (Vec.fromList [0x6d, 0x61]) =
    .needMore (some 16) := by rfl

def symbolHeader : Header := { amd64ObjectHeader with numberOfSymbols := 2 }

def twoCells : Vec SymbolCell :=
  Vec.fromList [mainCell, { mainCell with value := 0x20 }]

def symbolTable : SymbolTable symbolHeader where
  cells := twoCells
  cellCount := by rfl

example : (writeSymbolTable symbolTable).length = 36 := by
  exact length_writeSymbolTable symbolTable

example : readSymbolTable symbolHeader
    (writeSymbolTable symbolTable ++ Vec.fromList [0xaa]) =
    .done symbolTable (Vec.fromList [0xaa]) := by
  exact readSymbolTable_writeSymbolTable_append symbolTable _

example : readSymbolTable symbolHeader encodedMainCell =
    .needMore (some 18) := by rfl

example : Derives (symbolTableFormat symbolHeader)
    (writeSymbolTable symbolTable) symbolTable Vec.empty := by
  exact writeSymbolTable_derives symbolTable

end Grass.Tests.Artifact.COFF.Symbol
