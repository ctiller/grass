import Grass.Artifact.COFF.LineNumber
import Tests.Artifact.COFF.SectionHeader

/-! # COFF line-number and coupled-block fixtures -/

namespace Grass.Tests.Artifact.COFF.LineNumber

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.COFF.SectionHeader

def functionStart : Grass.Artifact.COFF.LineNumber := .functionSymbolIndex 3

def sourceLine : Grass.Artifact.COFF.LineNumber :=
  .sourceLine 0x20 12 (by decide)

example : writeLineNumber functionStart =
    Vec.fromList [0x03, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide

example : writeLineNumber sourceLine =
    Vec.fromList [0x20, 0x00, 0x00, 0x00, 0x0c, 0x00] := by decide

example : readLineNumber (writeLineNumber sourceLine ++ Vec.fromList [0xaa]) =
    .done sourceLine (Vec.fromList [0xaa]) := by
  exact readLineNumber_writeLineNumber_append sourceLine _

def lineSection : SectionHeader := { textSection with numberOfLineNumbers := 2 }

def lineBlock : LineNumberBlock lineSection where
  lines := Vec.fromList [functionStart, sourceLine]
  lineCount := by rfl

example : (writeLineNumberBlock lineBlock).length = 12 := by
  exact length_writeLineNumberBlock lineBlock

example : readLineNumberBlock lineSection
    (writeLineNumberBlock lineBlock ++ Vec.fromList [0xbb]) =
    .done lineBlock (Vec.fromList [0xbb]) := by
  exact readLineNumberBlock_write_append lineBlock _

example : readLineNumberBlock lineSection (writeLineNumber sourceLine) =
    .needMore (some 6) := by rfl

example : Derives (lineNumberBlockFormat lineSection)
    (writeLineNumberBlock lineBlock) lineBlock Vec.empty := by
  exact writeLineNumberBlock_derives lineBlock

end Grass.Tests.Artifact.COFF.LineNumber
