import Grass.Artifact.PE.OptionalHeader

/-! # Canonical PE32+ optional-header fixtures -/

namespace Grass.Tests.Artifact.PE.OptionalHeader

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def standard : Grass.Artifact.PE.OptionalHeaderStandard := {
  majorLinkerVersion := 14
  minorLinkerVersion := 0
  sizeOfCode := 0x200
  sizeOfInitializedData := 0x200
  sizeOfUninitializedData := 0
  addressOfEntryPoint := 0x1000
  baseOfCode := 0x1000
}

def windowsPrefix : Grass.Artifact.PE.OptionalHeaderWindowsPrefix := {
  imageBase := 0x0000000140000000
  sectionAlignment := 0x1000
  fileAlignment := 0x200
}

def versions : Grass.Artifact.PE.OptionalHeaderVersions := {
  majorOperatingSystemVersion := 6
  minorOperatingSystemVersion := 0
  majorImageVersion := 0
  minorImageVersion := 0
  majorSubsystemVersion := 6
  minorSubsystemVersion := 0
}

def imageFields : Grass.Artifact.PE.OptionalHeaderImageFields := {
  win32VersionValue := 0
  sizeOfImage := 0x3000
  sizeOfHeaders := 0x400
  checkSum := 0
}

def runtimeFields : Grass.Artifact.PE.OptionalHeaderRuntimeFields := {
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

def directoriesValue : Vec DataDirectory :=
  Vec.fromList (List.replicate 16 zeroDirectory)

theorem directoriesValue_length : directoriesValue.length = 16 := by decide

def directories : DataDirectoryTable :=
  ⟨directoriesValue, directoriesValue_length⟩

theorem runtimeDirectoryCount : runtimeFields.numberOfRvaAndSizes.toNat = 16 :=
  by decide

def header : Grass.Artifact.PE.OptionalHeader := {
  standard, windowsPrefix, versions, imageFields, runtimeFields, directories
  directoryCount := runtimeDirectoryCount
}

example : (writeOptionalHeader header).length = 240 := by simp

example : readOptionalHeader Vec.empty = .needMore (some 240) := by
  exact readOptionalHeader_short (by decide)

example : readOptionalHeader
    (writeOptionalHeader header ++ Vec.fromList [0xaa, 0xbb]) =
      .done header (Vec.fromList [0xaa, 0xbb]) := by
  simp

example : Derives optionalHeaderFormat
    (writeOptionalHeader header) header Vec.empty :=
  writeOptionalHeader_derives header

def noncanonicalRuntimeFields : Grass.Artifact.PE.OptionalHeaderRuntimeFields :=
  { runtimeFields with numberOfRvaAndSizes := 15 }

def noncanonicalBytes : Std.Logical.ByteArray :=
  writeOptionalHeaderStandard standard ++
  writeOptionalHeaderWindowsPrefix windowsPrefix ++
  writeOptionalHeaderVersions versions ++
  writeOptionalHeaderImageFields imageFields ++
  writeOptionalHeaderRuntimeFields noncanonicalRuntimeFields ++
  writeDataDirectoryTable directories

example : readOptionalHeader noncanonicalBytes =
    .invalid (.malformed
      "PE32+ canonical data-directory count mismatch") := by
  unfold noncanonicalBytes
  rw [readOptionalHeader]
  have enough : 240 ≤
      (writeOptionalHeaderStandard standard ++
        writeOptionalHeaderWindowsPrefix windowsPrefix ++
        writeOptionalHeaderVersions versions ++
        writeOptionalHeaderImageFields imageFields ++
        writeOptionalHeaderRuntimeFields noncanonicalRuntimeFields ++
        writeDataDirectoryTable directories).length := by
    simp
  simp only [Vec.append_assoc,
    readOptionalHeaderStandard_write_append,
    readOptionalHeaderWindowsPrefix_write_append,
    readOptionalHeaderVersions_write_append,
    readOptionalHeaderImageFields_write_append,
    readOptionalHeaderRuntimeFields_write_append]
  have parsed : readDataDirectoryTable (writeDataDirectoryTable directories) =
      .done directories Vec.empty := by
    simpa using readDataDirectoryTable_writeDataDirectoryTable_append
      directories Vec.empty
  rw [parsed]
  simp [noncanonicalRuntimeFields, runtimeFields]

end Grass.Tests.Artifact.PE.OptionalHeader
