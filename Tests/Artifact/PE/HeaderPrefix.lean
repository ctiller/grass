import Grass.Artifact.PE.HeaderPrefix

/-! # PE image-header prefix fixtures -/

namespace Grass.Tests.Artifact.PE.HeaderPrefix

open Grass.Artifact.COFF Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def amd64Header : Grass.Artifact.COFF.Header where
  machine := 0x8664
  numberOfSections := 3
  timeDateStamp := 0
  pointerToSymbolTable := 0
  numberOfSymbols := 0
  sizeOfOptionalHeader := 0xf0
  characteristics := 0x22

def imagePrefix : Grass.Artifact.PE.HeaderPrefix := ⟨amd64Header⟩

example : signatureBytes = Vec.fromList [0x50, 0x45, 0x00, 0x00] := rfl

example : readSignature (Vec.fromList [0x50, 0x45, 0x00]) =
    .needMore (some 1) := by
  exact readSignature_short (by decide)

example : readSignature (Vec.fromList [0x50, 0x45, 0x00, 0x01]) =
    .invalid (.malformed "PE signature mismatch") := by
  rfl

example : readSignature
    (signatureBytes ++ Vec.fromList [0xaa, 0xbb]) =
      .done () (Vec.fromList [0xaa, 0xbb]) := by
  change readSignature
      (writeSignature () ++ Vec.fromList [0xaa, 0xbb]) = _
  exact readSignature_writeSignature_append (Vec.fromList [0xaa, 0xbb])

example : (writeHeaderPrefix imagePrefix).length = 24 := by simp

example : readHeaderPrefix
    (writeHeaderPrefix imagePrefix ++ Vec.singleton 0xff) =
      .done imagePrefix (Vec.singleton 0xff) := by
  simp

example : Derives headerPrefixFormat (writeHeaderPrefix imagePrefix)
    imagePrefix Vec.empty :=
  writeHeaderPrefix_derives imagePrefix

end Grass.Tests.Artifact.PE.HeaderPrefix
