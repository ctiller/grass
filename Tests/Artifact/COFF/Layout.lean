import Grass.Artifact.COFF.Layout
import Tests.Artifact.COFF.SectionHeader
import Tests.Artifact.COFF.StringTable

/-! # COFF declared-span and layout-validation fixtures -/

namespace Grass.Tests.Artifact.COFF.Layout

open Grass.Artifact.Binary Grass.Artifact.COFF Grass.Std.Logical
open Grass.Tests.Artifact.COFF.SectionHeader
open Grass.Tests.Artifact.COFF.StringTable

def layoutHeader : Header where
  machine := 0x8664
  numberOfSections := 1
  timeDateStamp := 0
  pointerToSymbolTable := 86
  numberOfSymbols := 1
  sizeOfOptionalHeader := 0
  characteristics := 0

def layoutSection : SectionHeader := textSection

def layoutSections : Vec SectionHeader := Vec.singleton layoutSection

example : layoutHeader.prefixSpan = { offset := 0, length := 60 } := by decide

example : layoutSection.rawDataSpan = { offset := 60, length := 16 } := by decide

example : layoutSection.relocationSpan = { offset := 76, length := 10 } := by decide

example : layoutSection.lineNumberSpan = { offset := 0, length := 0 } := by decide

example : layoutHeader.symbolTableSpan = { offset := 86, length := 18 } := by decide

example : layoutHeader.stringTableSpan longNames =
    { offset := 104, length := 9 } := by decide

example : layoutSection.PointersCoherent := by decide

example : DeclaredLayoutValid layoutHeader layoutSections longNames 113 := by decide

def overlappingSection : SectionHeader :=
  { layoutSection with pointerToRawData := 50 }

example : ¬DeclaredLayoutValid layoutHeader
    (Vec.singleton overlappingSection) longNames 113 := by decide

def outOfBoundsHeader : Header :=
  { layoutHeader with pointerToSymbolTable := 100 }

example : ¬DeclaredLayoutValid outOfBoundsHeader layoutSections longNames 113 := by decide

def danglingLinePointer : SectionHeader :=
  { layoutSection with pointerToLineNumbers := 90 }

example : ¬danglingLinePointer.PointersCoherent := by decide

example : ¬DeclaredLayoutValid layoutHeader
    (Vec.singleton danglingLinePointer) longNames 113 := by decide

end Grass.Tests.Artifact.COFF.Layout
