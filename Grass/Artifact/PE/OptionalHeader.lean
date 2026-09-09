import Grass.Artifact.Binary.Endian
import Grass.Artifact.PE.Validation

/-!
# Canonical PE32+ optional header

This module synthesizes the fixed PE32+ fields from the typed image description
and its checked placements. Import-directory entries use the measured `.idata`
directory supplied by the import-table builder, or zero when no imports exist.

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

/-- Serialize one RVA/size data-directory entry. -/
def writeDataDirectory (rva size : Nat) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (BitVec.ofNat 32 rva) ++
    writeLittleEndian (count := 4) (BitVec.ofNat 32 size)

/-- Sixteen data-directory entries. The import entry is populated exactly when
imports were materialized; all other directories remain absent. -/
def writeDataDirectories (layout : ImageLayout) : Std.Logical.ByteArray :=
  let importRva := layout.importSectionRva.getD 0
  let importSize :=
    if layout.requested.imports.length = 0 then 0
    else importDescriptorTableSize layout.requested.imports.length
  writeDataDirectory 0 0 ++ writeDataDirectory importRva importSize ++
    Vec.replicate (14 * 8) 0

/-- Serialize the 240-byte PE32+ optional header for placements already derived
from `description`. -/
def writeOptionalHeader (layout : ImageLayout) : Std.Logical.ByteArray :=
  let sections := layout.placed.toList
  let headerSize := firstRawOffset canonicalPeOffset layout.placed.length canonicalFileAlignment
  -- Standard fields: 24 bytes.
  writeLittleEndian (count := 2) (0x020b : BitVec 16) ++
  Vec.fromList [14, 0] ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 (sumRawSizeWith containsCode sections)) ++
  writeLittleEndian (count := 4)
    (BitVec.ofNat 32 (sumRawSizeWith containsInitializedData sections)) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 layout.entryPointRva) ++
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
  writeLittleEndian (count := 4) (BitVec.ofNat 32 layout.sizeOfImage) ++
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
  writeDataDirectories layout

/-- `writeOptionalHeader` emits the exact PE32+ optional-header width. -/
@[simp] theorem length_writeOptionalHeader (layout : ImageLayout) :
    (writeOptionalHeader layout).length = optionalHeader64Size := by
  simp [writeOptionalHeader, writeDataDirectories, writeDataDirectory,
    optionalHeader64Size]

end Grass.Artifact.PE
