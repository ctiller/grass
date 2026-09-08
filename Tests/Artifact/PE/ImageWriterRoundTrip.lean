import Grass.Artifact.PE.ImageWriterRoundTrip
import Tests.Artifact.PE.ImageWriter

/-! # Canonical PE32+ image-writer round-trip fixtures -/

namespace Grass.Tests.Artifact.PE.ImageWriterRoundTrip

open Grass.Artifact.COFF Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

namespace WriterFixture

open Grass.Tests.Artifact.PE.ImageWriter

example : DeclaredImageLayoutValid
    (description.imageSectionTable description_writable.2.1) bytes.length := by
  exact description.layoutValid description_writable

example : readImage bytes =
    .done (description.image description_writable) Vec.empty := by
  exact description.readImage_bytes description_writable

example : ∃ image, readImage bytes = .done image Vec.empty := by
  have written : writeImageDescription description = .ok bytes := by
    unfold writeImageDescription
    rw [dif_pos description_writable]
    rfl
  exact readImage_writeImageDescription written

end WriterFixture

def emptySection : ImageSectionDescription :=
  { Grass.Tests.Artifact.PE.ImageWriter.textDescription with
    rawData := Vec.empty }

def emptyDescription : ImageDescription :=
  { Grass.Tests.Artifact.PE.ImageWriter.description with
    sections := Vec.singleton emptySection }

theorem emptyDescription_fileAlignment :
    emptyDescription.fileAlignment = 512 := by rfl

theorem emptyDescription_firstRawDataOffset :
    emptyDescription.firstRawDataOffset = 512 := by rfl

theorem emptyDescription_sections_toList :
    emptyDescription.sections.toList = [emptySection] := by rfl

theorem emptySection_alignedRawData_length :
    alignUp emptySection.rawData.length 512 = 0 := by decide

theorem emptyDescription_writable : emptyDescription.Writable := by
  unfold ImageDescription.Writable
  rw [emptyDescription_fileAlignment, emptyDescription_firstRawDataOffset]
  change 0 < 512 ∧ 1 < 2 ^ 16 ∧ 512 < 2 ^ 32 ∧
    imageSectionPlacementsFit 512 512 [emptySection] = true
  simp [imageSectionPlacementsFit, emptySection_alignedRawData_length]

def emptyBytes : Std.Logical.ByteArray :=
  emptyDescription.bytes emptyDescription_writable.2.1

example : emptyBytes.length = 512 := by
  unfold emptyBytes
  rw [emptyDescription.length_bytes emptyDescription_writable.2.1]
  unfold ImageDescription.sectionLayout
  rw [layoutImageSectionList_end]
  rw [emptyDescription_firstRawDataOffset, emptyDescription_fileAlignment,
    emptyDescription_sections_toList]
  simp [imageSectionDescriptionListLength, emptySection_alignedRawData_length]

example : readImage emptyBytes =
    .done (emptyDescription.image emptyDescription_writable) Vec.empty := by
  exact emptyDescription.readImage_bytes emptyDescription_writable

def zeroAlignmentDescription : ImageDescription :=
  { Grass.Tests.Artifact.PE.ImageWriter.description with
    optionalHeader :=
      { Grass.Tests.Artifact.PE.ImageWriter.description.optionalHeader with
        windowsPrefix :=
          { Grass.Tests.Artifact.PE.ImageWriter.description.optionalHeader.windowsPrefix with
            fileAlignment := 0 } } }

theorem zeroAlignmentDescription_fileAlignment :
    zeroAlignmentDescription.fileAlignment = 0 := by rfl

example : writeImageDescription zeroAlignmentDescription =
    .error (.arithmeticOverflow
      "PE32+ image layout exceeds field width or has zero file alignment") := by
  unfold writeImageDescription
  rw [dif_neg]
  intro writable
  unfold ImageDescription.Writable at writable
  rw [zeroAlignmentDescription_fileAlignment] at writable
  omega

end Grass.Tests.Artifact.PE.ImageWriterRoundTrip
