import Grass.Artifact.PE.ImageHeaders

/-! # Canonical PE32+ image-header fixtures -/

namespace Grass.Tests.Artifact.PE.ImageHeaders

open Grass.Artifact.COFF Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def fileHeader : Grass.Artifact.COFF.Header where
  machine := 0x8664
  numberOfSections := 1
  timeDateStamp := 0
  pointerToSymbolTable := 0
  numberOfSymbols := 0
  sizeOfOptionalHeader := 240
  characteristics := 0x22

def imagePrefix : HeaderPrefix := ⟨fileHeader⟩

def standard : OptionalHeaderStandard := {
  majorLinkerVersion := 14
  minorLinkerVersion := 0
  sizeOfCode := 0x200
  sizeOfInitializedData := 0x200
  sizeOfUninitializedData := 0
  addressOfEntryPoint := 0x1000
  baseOfCode := 0x1000
}

def windowsPrefix : OptionalHeaderWindowsPrefix := {
  imageBase := 0x0000000140000000
  sectionAlignment := 0x1000
  fileAlignment := 0x200
}

def versions : OptionalHeaderVersions := {
  majorOperatingSystemVersion := 6
  minorOperatingSystemVersion := 0
  majorImageVersion := 0
  minorImageVersion := 0
  majorSubsystemVersion := 6
  minorSubsystemVersion := 0
}

def imageFields : OptionalHeaderImageFields := {
  win32VersionValue := 0
  sizeOfImage := 0x2000
  sizeOfHeaders := 0x200
  checkSum := 0
}

def runtimeFields : OptionalHeaderRuntimeFields := {
  subsystem := 3
  dllCharacteristics := 0x8160
  sizeOfStackReserve := 0x100000
  sizeOfStackCommit := 0x1000
  sizeOfHeapReserve := 0x100000
  sizeOfHeapCommit := 0x1000
  loaderFlags := 0
  numberOfRvaAndSizes := 16
}

def zeroDirectory : DataDirectory := ⟨0, 0⟩

def directoryValues : Vec DataDirectory :=
  Vec.fromList (List.replicate 16 zeroDirectory)

theorem directoryValues_length : directoryValues.length = 16 := by decide

def directories : DataDirectoryTable :=
  ⟨directoryValues, directoryValues_length⟩

def optionalHeader : OptionalHeader := {
  standard, windowsPrefix, versions, imageFields, runtimeFields, directories
  directoryCount := by decide
}

def headers : Grass.Artifact.PE.ImageHeaders := {
  headerPrefix := imagePrefix
  optionalHeader
  optionalHeaderSize := by decide
}

example : (writeImageHeaders headers).length = 264 := by simp

example : readImageHeaders Vec.empty = .needMore (some 264) := by
  exact readImageHeaders_short (by decide)

example : readImageHeaders
    (writeImageHeaders headers ++ Vec.singleton 0xaa) =
      .done headers (Vec.singleton 0xaa) := by
  simp

example : Derives imageHeadersFormat
    (writeImageHeaders headers) headers Vec.empty :=
  writeImageHeaders_derives headers

def wrongSizeFileHeader : Grass.Artifact.COFF.Header :=
  { fileHeader with sizeOfOptionalHeader := 224 }

def wrongSizeBytes : Std.Logical.ByteArray :=
  writeHeaderPrefix ⟨wrongSizeFileHeader⟩ ++
  writeOptionalHeader optionalHeader

example : readImageHeaders wrongSizeBytes =
    .invalid (.malformed "PE32+ optional-header size mismatch") := by
  unfold wrongSizeBytes
  rw [readImageHeaders]
  simp only [Vec.length_append, length_writeHeaderPrefix,
    length_writeOptionalHeader]
  simp only [show 264 ≤ 24 + 240 by decide, ite_true,
    readHeaderPrefix_writeHeaderPrefix_append]
  have parsed : readOptionalHeader (writeOptionalHeader optionalHeader) =
      .done optionalHeader Vec.empty := readOptionalHeader_write optionalHeader
  rw [parsed]
  simp [wrongSizeFileHeader, fileHeader]

end Grass.Tests.Artifact.PE.ImageHeaders
