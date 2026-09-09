import Grass.Artifact.Binary.Endian
import Grass.Artifact.PE.Layout

/-!
# Canonical PE32+ file prefix

This module serializes the complete-file DOS prefix, PE signature, and COFF
file header. All offsets are absolute and the emitted `e_lfanew` agrees with
`canonicalPeOffset` from `Grass.Artifact.PE.Layout`.

Format authority: Microsoft, [PE Format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format),
sections "MS-DOS Stub (Image Only)", "Signature (Image Only)", and "COFF File
Header (Object and Image)"; retrieved 2026-09-01 in `docs/REFERENCES.md`.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical Grass.Artifact.Binary

/-- `IMAGE_FILE_MACHINE_AMD64`. This is a PE/COFF container discriminator; it
does not describe or encode an instruction. -/
def amd64Machine : BitVec 16 := 0x8664

/-- `IMAGE_FILE_EXECUTABLE_IMAGE | IMAGE_FILE_LARGE_ADDRESS_AWARE`. -/
def executableImageCharacteristics : BitVec 16 := 0x0022

/-- Canonical 64-byte DOS prefix. It contains `MZ`, zeroed compatibility fields,
and the absolute NT-header offset at byte 60. -/
def writeCanonicalDosHeader : Std.Logical.ByteArray :=
  Vec.fromList [0x4d, 0x5a] ++ Vec.replicate 58 0 ++
    writeLittleEndian (count := 4) (BitVec.ofNat 32 canonicalPeOffset)

/-- `writeCanonicalDosHeader` is exactly the region whose end is
`canonicalPeOffset`. -/
@[simp] theorem length_writeCanonicalDosHeader :
    writeCanonicalDosHeader.length = canonicalPeOffset := by
  simp [writeCanonicalDosHeader, canonicalPeOffset]

/-- The four-byte PE signature `PE\0\0`. -/
def writePeSignature : Std.Logical.ByteArray := Vec.fromList [0x50, 0x45, 0, 0]

/-- Serialize the twenty-byte COFF file header used by a PE32+ executable. -/
def writeImageCoffHeader (sectionCount : BitVec 16) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 2) amd64Machine ++
  writeLittleEndian (count := 2) sectionCount ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 2) (240 : BitVec 16) ++
  writeLittleEndian (count := 2) executableImageCharacteristics

/-- `writeImageCoffHeader` emits the fixed twenty-byte COFF header. -/
@[simp] theorem length_writeImageCoffHeader (sectionCount : BitVec 16) :
    (writeImageCoffHeader sectionCount).length = coffHeaderSize := by
  simp [writeImageCoffHeader, coffHeaderSize]

/-- Fixed bytes through the COFF machine field, immediately before the section
count. -/
def writeHeaderPrefixLeading : Std.Logical.ByteArray :=
  writeCanonicalDosHeader ++ writePeSignature ++
    writeLittleEndian (count := 2) amd64Machine

@[simp] theorem length_writeHeaderPrefixLeading : writeHeaderPrefixLeading.length = 70 := by
  simp [writeHeaderPrefixLeading, writePeSignature, canonicalPeOffset]

/-- Fixed COFF fields after the section count. -/
def writeHeaderPrefixTrailing : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 2) (240 : BitVec 16) ++
  writeLittleEndian (count := 2) executableImageCharacteristics

@[simp] theorem length_writeHeaderPrefixTrailing : writeHeaderPrefixTrailing.length = 16 := by
  simp [writeHeaderPrefixTrailing]

/-- Serialize the complete prefix before the PE32+ optional header. -/
def writeHeaderPrefix (sectionCount : BitVec 16) : Std.Logical.ByteArray :=
  writeHeaderPrefixLeading ++ writeLittleEndian (count := 2) sectionCount ++
    writeHeaderPrefixTrailing

/-- The canonical prefix is 64 DOS bytes, four signature bytes, and twenty COFF
header bytes. -/
@[simp] theorem length_writeHeaderPrefix (sectionCount : BitVec 16) :
    (writeHeaderPrefix sectionCount).length =
      canonicalPeOffset + peSignatureSize + coffHeaderSize := by
  simp [writeHeaderPrefix, canonicalPeOffset, peSignatureSize, coffHeaderSize]

end Grass.Artifact.PE
