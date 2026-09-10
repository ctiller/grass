import Grass.Artifact.ELF.Header

namespace Tests.Artifact.ELF.Header
open Grass.Artifact.ELF Grass.Grammar Grass.Std.Logical

def header (machine : BitVec 16) : Header64 where
  ident := ident64LE
  objectType := 2
  machine := machine
  version := 1
  entry := 0x401000
  programOffset := 64
  sectionOffset := 0
  flags := 0
  headerSize := 64
  programEntrySize := 56
  programCount := 1
  sectionEntrySize := 0
  sectionCount := 0
  stringSectionIndex := 0

example : (writeHeader64 (header 62)).length = 64 := writeHeader64_length _

example : readHeader64 (writeHeader64 (header 62) ++ Vec.fromList [0xa5]) =
    .done (header 62) (Vec.fromList [0xa5]) :=
  readHeader64_write_append _ (by decide) _

example : readHeader64 (writeHeader64 (header 183) ++ Vec.fromList [0x5a]) =
    .done (header 183) (Vec.fromList [0x5a]) :=
  readHeader64_write_append _ (by decide) _

/-- Check the independent ELF field offsets rather than only a writer round trip. -/
example : (writeHeader64 (header 183)).get? 18 = some 183 := by decide
example : (writeHeader64 (header 62)).get? 24 = some 0 := by decide
example : (writeHeader64 (header 62)).get? 26 = some 0x40 := by decide
example : (writeHeader64 (header 62)).get? 32 = some 64 := by decide
example : (writeHeader64 (header 62)).get? 52 = some 64 := by decide

def unsupported (bytes : Grass.Std.Logical.ByteArray) : Bool :=
  match readHeader64 bytes with
  | .invalid (.unsupported _) => true
  | _ => false

example : unsupported ((writeHeader64 (header 62)).set 0 0) = true := by decide
example : unsupported ((writeHeader64 (header 62)).set 4 1) = true := by decide
example : unsupported ((writeHeader64 (header 62)).set 5 2) = true := by decide
example : unsupported ((writeHeader64 (header 62)).set 20 2) = true := by decide
example : unsupported ((writeHeader64 (header 62)).set 52 63) = true := by decide
example : unsupported (Vec.fromList [0]) = true := by decide
example : unsupported (((writeHeader64 (header 62)).set 20 2).take 21) = true := by decide

def truncated : Bool :=
  match readHeader64 ((writeHeader64 (header 62)).take 63) with
  | .needMore (some 1) => true
  | _ => false

example : truncated = true := by decide

example : readHeader64 Vec.empty = .needMore (some 64) := rfl
example : readHeader64 ((writeHeader64 (header 62)).take 15) =
    .needMore (some 49) := rfl

end Tests.Artifact.ELF.Header
