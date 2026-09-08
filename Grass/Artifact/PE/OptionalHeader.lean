import Grass.Artifact.Binary.Endian
import Grass.Artifact.PE.Validation

/-!
# Canonical PE32+ optional header

This module synthesizes the fixed PE32+ fields from the typed image description
and its checked placements. Import-directory entries remain zero until the
owned import-table builder supplies a measured `.idata` directory.

Format authority: Microsoft, [PE Format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format),
sections "Optional Header Standard Fields (Image Only)", "Optional Header
Windows-Specific Fields (Image Only)", and "Optional Header Data Directories
(Image Only)"; retrieved 2026-09-01 in `docs/REFERENCES.md`.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical Grass.Artifact.Binary

/-- `IMAGE_SCN_CNT_CODE`. -/
def containsCode : BitVec 32 := 0x00000020

/-- `IMAGE_SCN_CNT_INITIALIZED_DATA`. -/
def containsInitializedData : BitVec 32 := 0x00000040

/-- Sum padded raw extents carrying a selected section characteristic. -/
def sumRawSizeWith (flag : BitVec 32) : List PlacedSection → Nat
  | [] => 0
  | placed :: tail =>
      (if placed.source.characteristics &&& flag = 0 then 0 else placed.rawSpan.size) +
        sumRawSizeWith flag tail

/-- Select the first RVA carrying a section characteristic, or zero. -/
def firstVirtualStartWith (flag : BitVec 32) : List PlacedSection → Nat
  | [] => 0
  | placed :: tail =>
      if placed.source.characteristics &&& flag = 0 then
        firstVirtualStartWith flag tail
      else placed.virtualSpan.start

/-- Largest exclusive virtual end, retaining the aligned header page for an
empty image. -/
def greatestVirtualEnd : List PlacedSection → Nat
  | [] => canonicalSectionAlignment
  | placed :: tail => max placed.virtualSpan.endOffset (greatestVirtualEnd tail)

/-- Complete mapped image size rounded to section alignment. -/
def sizeOfImage (placed : Vec PlacedSection) : Nat :=
  alignUp (greatestVirtualEnd placed.toList) canonicalSectionAlignment

/-- Sixteen absent data-directory entries. `writeZeroDataDirectories` has the
exact 128-byte extent required by a header declaring sixteen entries. -/
def writeZeroDataDirectories : Std.Logical.ByteArray := Vec.replicate (16 * 8) 0

/-- Serialize the 240-byte PE32+ optional header for placements already derived
from `description`. -/
def writeOptionalHeader (description : ExecutableImageDescription)
    (placed : Vec PlacedSection) : Std.Logical.ByteArray :=
  let sections := placed.toList
  let headerSize := firstRawOffset canonicalPeOffset placed.length canonicalFileAlignment
  -- Standard fields: 24 bytes.
  writeLittleEndian (count := 2) (0x020b : BitVec 16) ++
  Vec.fromList [14, 0] ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 (sumRawSizeWith containsCode sections)) ++
  writeLittleEndian (count := 4)
    (BitVec.ofNat 32 (sumRawSizeWith containsInitializedData sections)) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) description.entryPointRva ++
  writeLittleEndian (count := 4)
    (BitVec.ofNat 32 (firstVirtualStartWith containsCode sections)) ++
  -- Windows-specific fields: 88 bytes.
  writeLittleEndian (count := 8) (0x0000000140000000 : BitVec 64) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 canonicalSectionAlignment) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 canonicalFileAlignment) ++
  writeLittleEndian (count := 2) (6 : BitVec 16) ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeLittleEndian (count := 2) (6 : BitVec 16) ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 (sizeOfImage placed)) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 headerSize) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 2) (3 : BitVec 16) ++
  writeLittleEndian (count := 2) (0x8160 : BitVec 16) ++
  writeLittleEndian (count := 8) (0x100000 : BitVec 64) ++
  writeLittleEndian (count := 8) (0x1000 : BitVec 64) ++
  writeLittleEndian (count := 8) (0x100000 : BitVec 64) ++
  writeLittleEndian (count := 8) (0x1000 : BitVec 64) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (16 : BitVec 32) ++
  writeZeroDataDirectories

/-- `writeOptionalHeader` emits the exact PE32+ optional-header width. -/
@[simp] theorem length_writeOptionalHeader (description : ExecutableImageDescription)
    (placed : Vec PlacedSection) :
    (writeOptionalHeader description placed).length = optionalHeader64Size := by
  simp [writeOptionalHeader, writeZeroDataDirectories, optionalHeader64Size]

end Grass.Artifact.PE
