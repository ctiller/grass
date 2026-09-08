import Grass.Artifact.COFF.SymbolName

/-! # Typed COFF symbol-name fixtures -/

namespace Grass.Tests.Artifact.COFF.SymbolName

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

def inlineMain : Grass.Artifact.COFF.SymbolName :=
  SymbolName.ofWords (0x6e69616d, 0x00000000)

def longName : Grass.Artifact.COFF.SymbolName :=
  .stringTableOffset 0x1234

example : writeSymbolName inlineMain = Vec.fromList [
    0x6d, 0x61, 0x69, 0x6e, 0x00, 0x00, 0x00, 0x00] := by decide

example : readSymbolName (Vec.fromList [
    0x6d, 0x61, 0x69, 0x6e, 0x00, 0x00, 0x00, 0x00]) =
    .done inlineMain Vec.empty := by rfl

example : writeSymbolName longName = Vec.fromList [
    0x00, 0x00, 0x00, 0x00, 0x34, 0x12, 0x00, 0x00] := by decide

example : readSymbolName (Vec.fromList [
    0x00, 0x00, 0x00, 0x00, 0x34, 0x12, 0x00, 0x00, 0xaa]) =
    .done longName (Vec.fromList [0xaa]) := by rfl

example : readSymbolName (Vec.fromList [0x00, 0x00, 0x00]) =
    .needMore (some 5) := by rfl

def typedMain : Symbol where
  name := inlineMain
  value := 0x10
  sectionNumber := 1
  symbolType := 0x20
  storageClass := 2
  numberOfAuxSymbols := 0

example : writeSymbol typedMain = Vec.fromList [
    0x6d, 0x61, 0x69, 0x6e, 0x00, 0x00, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x01, 0x00, 0x20, 0x00, 0x02, 0x00] := by decide

example : readSymbol (writeSymbol typedMain ++ Vec.fromList [0xbb]) =
    .done typedMain (Vec.fromList [0xbb]) := by
  exact readSymbol_writeSymbol_append typedMain _

example : Derives symbolFormat (writeSymbol typedMain) typedMain Vec.empty := by
  exact writeSymbol_derives typedMain

end Grass.Tests.Artifact.COFF.SymbolName
