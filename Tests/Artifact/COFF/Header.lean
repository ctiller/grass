import Grass.Artifact.COFF.Header

/-! # COFF file-header fixtures -/

namespace Grass.Tests.Artifact.COFF.Header

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

def amd64ObjectHeader : Header where
  machine := 0x8664
  numberOfSections := 3
  timeDateStamp := 0x12345678
  pointerToSymbolTable := 0x20
  numberOfSymbols := 5
  sizeOfOptionalHeader := 0
  characteristics := 0x0004

def encodedHeader : Std.Logical.ByteArray := Vec.fromList [
  0x64, 0x86, 0x03, 0x00, 0x78, 0x56, 0x34, 0x12,
  0x20, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x04, 0x00]

example : writeHeader amd64ObjectHeader = encodedHeader := by decide

example : readHeader encodedHeader = .done amd64ObjectHeader Vec.empty := by rfl

example : readHeader (encodedHeader ++ Vec.fromList [0xaa, 0xbb]) =
    .done amd64ObjectHeader (Vec.fromList [0xaa, 0xbb]) := by rfl

example : readHeader Vec.empty = .needMore (some 20) := by rfl

example : readHeader (Vec.fromList [0x64, 0x86, 0x03]) =
    .needMore (some 17) := by rfl

example : (writeHeader amd64ObjectHeader).length = 20 := by
  exact length_writeHeader amd64ObjectHeader

example : readHeader (writeHeader amd64ObjectHeader) =
    .done amd64ObjectHeader Vec.empty := by
  exact readHeader_writeHeader amd64ObjectHeader

example : Derives headerFormat (writeHeader amd64ObjectHeader)
    amd64ObjectHeader Vec.empty := by
  exact writeHeader_derives amd64ObjectHeader

end Grass.Tests.Artifact.COFF.Header
