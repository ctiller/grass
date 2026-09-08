import Grass.Artifact.PE.Image
import Tests.Artifact.PE.ImageSectionTable

/-! # Parsed PE32+ image fixtures -/

namespace Grass.Tests.Artifact.PE.Image

open Grass.Artifact.COFF Grass.Artifact.PE Grass.Std.Logical

def smallSection : SectionHeader :=
  { Grass.Tests.Artifact.PE.ImageSectionTable.textSection with
    sizeOfRawData := 4
    pointerToRawData := 304 }

def smallTable : ImageSectionTable where
  headers := Grass.Tests.Artifact.PE.ImageSectionTable.table.headers
  sections := Vec.singleton smallSection
  sectionCount := by rfl

def payloadBytes : Std.Logical.ByteArray := Vec.fromList [1, 2, 3, 4]

theorem payloadBytes_length : payloadBytes.length = 4 := by decide

def payload : SectionRawData smallSection :=
  ⟨payloadBytes, payloadBytes_length⟩

def sectionContents : ImageSectionContents := ⟨smallSection, payload⟩

def imageBytes : Std.Logical.ByteArray :=
  writeImageSectionTable smallTable ++ payloadBytes

/-- The one-section header and table occupy exactly 304 bytes. -/
theorem length_writeSmallTable :
    (writeImageSectionTable smallTable).length = 304 := by
  rw [length_writeImageSectionTable]
  change 264 + 40 * 1 = 304
  decide

/-- The complete fixture adds its four-byte addressed payload. -/
theorem imageBytes_length : imageBytes.length = 308 := by
  unfold imageBytes
  rw [Vec.length_append, length_writeSmallTable, payloadBytes_length]

/-- The payload fixture occupies bytes 304 through 307 of `imageBytes`. -/
theorem read_sectionContents :
    readImageSectionContents smallSection imageBytes =
    .done sectionContents Vec.empty := by
  apply readImageSectionContents_of_region sectionContents imageBytes Vec.empty
  · change 304 + 4 ≤ imageBytes.length
    rw [imageBytes_length]
    omega
  · unfold imageBytes
    rw [Vec.drop_append_of_length_eq]
    · rfl
    · exact length_writeSmallTable

example : imageBytes.length = 308 := imageBytes_length

example : DeclaredImageLayoutValid smallTable imageBytes.length := by
  rw [imageBytes_length]
  decide

example : readImageSectionContents smallSection imageBytes =
    .done sectionContents Vec.empty := read_sectionContents

/-- The single addressed payload composes into the ordered content list. -/
theorem read_contentsList :
    readImageSectionContentsList smallTable.sections.toList imageBytes =
    .done [sectionContents] Vec.empty := by
  change readImageSectionContentsList [smallSection] imageBytes = _
  simp only [readImageSectionContentsList, read_sectionContents]

example : ∃ image, readImage imageBytes = .done image Vec.empty ∧
    image.bytes = imageBytes ∧ image.table = smallTable ∧
    image.contents = Vec.singleton sectionContents := by
  have parsedTable : readImageSectionTable imageBytes =
      .done smallTable payloadBytes := by
    unfold imageBytes
    exact readImageSectionTable_write_append smallTable payloadBytes
  unfold readImage
  rw [parsedTable]
  simp only
  rw [read_contentsList]
  simp only
  have valid : DeclaredImageLayoutValid smallTable imageBytes.length := by
    rw [imageBytes_length]
    decide
  simp only [valid, ↓reduceDIte]
  refine ⟨_, rfl, rfl, rfl, rfl⟩

end Grass.Tests.Artifact.PE.Image
