import Grass.Artifact.PE.ReaderCore
import Grass.Artifact.PE.OptionalHeader

/-! # Independent PE32+ optional-header field reader

Every emitted field is decoded, including reserved bytes and absent directories.
This reader reports the fields; loader applicability is a separate obligation.
-/

namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical Grass.Artifact.Binary

/-- The complete fixed-size optional header, retaining all directory bytes. -/
structure ParsedOptionalHeader where
  magic : BitVec 16
  linkerVersion : Std.Logical.ByteArray
  sizeOfCode : BitVec 32
  sizeOfInitializedData : BitVec 32
  sizeOfUninitializedData : BitVec 32
  entryPointRva : BitVec 32
  baseOfCode : BitVec 32
  imageBase : BitVec 64
  sectionAlignment : BitVec 32
  fileAlignment : BitVec 32
  majorOSVersion : BitVec 16
  minorOSVersion : BitVec 16
  majorImageVersion : BitVec 16
  minorImageVersion : BitVec 16
  majorSubsystemVersion : BitVec 16
  minorSubsystemVersion : BitVec 16
  win32Version : BitVec 32
  sizeOfImage : BitVec 32
  sizeOfHeaders : BitVec 32
  checksum : BitVec 32
  subsystem : BitVec 16
  dllCharacteristics : BitVec 16
  stackReserve : BitVec 64
  stackCommit : BitVec 64
  heapReserve : BitVec 64
  heapCommit : BitVec 64
  loaderFlags : BitVec 32
  directoryCount : BitVec 32
  exportRva : BitVec 32
  exportSize : BitVec 32
  importRva : BitVec 32
  importSize : BitVec 32
  remainingDirectories : Std.Logical.ByteArray
deriving DecidableEq, Repr

/-- Decode the complete 240-byte PE32+ header independently of serialization. -/
def readOptionalHeader (input : Std.Logical.ByteArray) : ParseResult ParsedOptionalHeader :=
  continueRead (takeLittleEndian 2 input) fun magic input =>
  continueRead (takeExact 2 input) fun linkerVersion input =>
  continueRead (takeLittleEndian 4 input) fun sizeOfCode input =>
  continueRead (takeLittleEndian 4 input) fun sizeOfInitializedData input =>
  continueRead (takeLittleEndian 4 input) fun sizeOfUninitializedData input =>
  continueRead (takeLittleEndian 4 input) fun entryPointRva input =>
  continueRead (takeLittleEndian 4 input) fun baseOfCode input =>
  continueRead (takeLittleEndian 8 input) fun imageBase input =>
  continueRead (takeLittleEndian 4 input) fun sectionAlignment input =>
  continueRead (takeLittleEndian 4 input) fun fileAlignment input =>
  continueRead (takeLittleEndian 2 input) fun majorOSVersion input =>
  continueRead (takeLittleEndian 2 input) fun minorOSVersion input =>
  continueRead (takeLittleEndian 2 input) fun majorImageVersion input =>
  continueRead (takeLittleEndian 2 input) fun minorImageVersion input =>
  continueRead (takeLittleEndian 2 input) fun majorSubsystemVersion input =>
  continueRead (takeLittleEndian 2 input) fun minorSubsystemVersion input =>
  continueRead (takeLittleEndian 4 input) fun win32Version input =>
  continueRead (takeLittleEndian 4 input) fun sizeOfImage input =>
  continueRead (takeLittleEndian 4 input) fun sizeOfHeaders input =>
  continueRead (takeLittleEndian 4 input) fun checksum input =>
  continueRead (takeLittleEndian 2 input) fun subsystem input =>
  continueRead (takeLittleEndian 2 input) fun dllCharacteristics input =>
  continueRead (takeLittleEndian 8 input) fun stackReserve input =>
  continueRead (takeLittleEndian 8 input) fun stackCommit input =>
  continueRead (takeLittleEndian 8 input) fun heapReserve input =>
  continueRead (takeLittleEndian 8 input) fun heapCommit input =>
  continueRead (takeLittleEndian 4 input) fun loaderFlags input =>
  continueRead (takeLittleEndian 4 input) fun directoryCount input =>
  continueRead (takeLittleEndian 4 input) fun exportRva input =>
  continueRead (takeLittleEndian 4 input) fun exportSize input =>
  continueRead (takeLittleEndian 4 input) fun importRva input =>
  continueRead (takeLittleEndian 4 input) fun importSize input =>
  continueRead (takeExact 112 input) fun remainingDirectories input =>
  .done { magic, linkerVersion, sizeOfCode, sizeOfInitializedData, sizeOfUninitializedData, entryPointRva, baseOfCode, imageBase, sectionAlignment, fileAlignment, majorOSVersion, minorOSVersion, majorImageVersion, minorImageVersion, majorSubsystemVersion, minorSubsystemVersion, win32Version, sizeOfImage, sizeOfHeaders, checksum, subsystem, dllCharacteristics, stackReserve, stackCommit, heapReserve, heapCommit, loaderFlags, directoryCount, exportRva, exportSize, importRva, importSize, remainingDirectories } input

/-- The field values synthesized from the single image layout. -/
def expectedOptionalHeader (layout : ImageLayout) : ParsedOptionalHeader where
  magic := 0x020b
  linkerVersion := Vec.fromList [14, 0]
  sizeOfCode := BitVec.ofNat 32 (sumRawSizeWith containsCode layout.placed.toList)
  sizeOfInitializedData := BitVec.ofNat 32 (sumRawSizeWith containsInitializedData layout.placed.toList)
  sizeOfUninitializedData := 0
  entryPointRva := BitVec.ofNat 32 layout.entryPointRva
  baseOfCode := BitVec.ofNat 32 (firstVirtualStartWith containsCode layout.placed.toList)
  imageBase := 0x0000000140000000
  sectionAlignment := BitVec.ofNat 32 canonicalSectionAlignment
  fileAlignment := BitVec.ofNat 32 canonicalFileAlignment
  majorOSVersion := 6
  minorOSVersion := 0
  majorImageVersion := 0
  minorImageVersion := 0
  majorSubsystemVersion := 6
  minorSubsystemVersion := 0
  win32Version := 0
  sizeOfImage := BitVec.ofNat 32 layout.sizeOfImage
  sizeOfHeaders := BitVec.ofNat 32 (firstRawOffset canonicalPeOffset layout.placed.length canonicalFileAlignment)
  checksum := 0
  subsystem := 3
  dllCharacteristics := 0x8160
  stackReserve := 0x100000
  stackCommit := 0x1000
  heapReserve := 0x100000
  heapCommit := 0x1000
  loaderFlags := 0
  directoryCount := 16
  exportRva := 0
  exportSize := 0
  importRva := BitVec.ofNat 32 (layout.importSectionRva.getD 0)
  importSize := BitVec.ofNat 32 (if layout.requested.imports.length = 0 then 0 else importDescriptorTableSize layout.requested.imports.length)
  remainingDirectories := Vec.replicate (14 * 8) 0

/-- `readOptionalHeader_write_append` proves full field recovery with an arbitrary suffix. -/
theorem readOptionalHeader_write_append (layout : ImageLayout)
    (suffix : Std.Logical.ByteArray) :
    readOptionalHeader (writeOptionalHeader layout ++ suffix) =
      .done (expectedOptionalHeader layout) suffix := by
  simp only [readOptionalHeader, writeOptionalHeader, writeDataDirectories,
    writeDataDirectory, Vec.append_assoc, takeLittleEndian_writeLittleEndian_append,
    continueRead]
  rw [takeExact_append (by simp : (Vec.fromList [14, 0] : Std.Logical.ByteArray).length = 2)]
  simp only [takeLittleEndian_writeLittleEndian_append]
  rw [takeExact_append (by simp : (Vec.replicate (14 * 8) (0 : Byte)).length = 112)]
  rfl

end Grass.Artifact.PE
