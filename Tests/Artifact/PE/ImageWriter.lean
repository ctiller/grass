import Grass.Artifact.PE.ImageWriter
import Tests.Artifact.PE.ImageHeaders

/-! # Canonical PE32+ image-writer fixtures -/

namespace Grass.Tests.Artifact.PE.ImageWriter

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

def textNameBytes : Std.Logical.ByteArray :=
  Vec.fromList [0x2e, 0x74, 0x65, 0x78, 0x74, 0x00, 0x00, 0x00]

theorem textNameBytes_length : textNameBytes.length = 8 := by decide

def textDescription : ImageSectionDescription where
  name := ⟨textNameBytes, textNameBytes_length⟩
  virtualSize := 4
  virtualAddress := 0x1000
  rawData := Vec.fromList [1, 2, 3, 4]
  characteristics := 0x60000020

def description : ImageDescription where
  machine := 0x8664
  timeDateStamp := 0
  characteristics := 0x22
  optionalHeader := Grass.Tests.Artifact.PE.ImageHeaders.optionalHeader
  sections := Vec.singleton textDescription

theorem description_fileAlignment : description.fileAlignment = 512 := by rfl

theorem description_firstRawDataOffset :
    description.firstRawDataOffset = 512 := by rfl

theorem textDescription_paddedRawData_length :
    (textDescription.paddedRawData 512).length = 512 := by
  rw [ImageSectionDescription.paddedRawData, length_padBytes]
  decide

theorem textDescription_alignedRawData_length :
    alignUp textDescription.rawData.length 512 = 512 := by decide

theorem description_sections_toList :
    description.sections.toList = [textDescription] := by rfl

theorem description_writable : description.Writable := by
  unfold ImageDescription.Writable
  rw [description_fileAlignment, description_firstRawDataOffset]
  change 0 < 512 ∧ 1 < 2 ^ 16 ∧ 512 < 2 ^ 32 ∧
    imageSectionPlacementsFit 512 512 [textDescription] = true
  simp [imageSectionPlacementsFit, textDescription_alignedRawData_length]

def table : ImageSectionTable :=
  description.imageSectionTable description_writable.2.1

def bytes : Std.Logical.ByteArray :=
  description.bytes description_writable.2.1

theorem table_sections :
    table.sections = Vec.singleton (textDescription.headerAt 512 512) := by
  change Vec.fromList (layoutImageSectionList description.fileAlignment
    description.firstRawDataOffset description.sections.toList).1 = _
  rw [description_fileAlignment, description_firstRawDataOffset,
    description_sections_toList, layoutImageSectionList_singleton]
  rfl

example : alignUp 304 512 = 512 := by decide

example : description.firstRawDataOffset = 512 :=
  description_firstRawDataOffset

example : (textDescription.paddedRawData description.fileAlignment).length =
    512 := by
  rw [description_fileAlignment]
  exact textDescription_paddedRawData_length

example : table.sections.length = 1 := by
  change description.sectionLayout.1.length = 1
  rw [description.length_sectionLayout]
  rfl

example : (table.sections.get? 0).map
    (fun entry => entry.pointerToRawData.toNat) = some 512 := by
  rw [table_sections]
  simp [textDescription_paddedRawData_length]

example : (table.sections.get? 0).map
    (fun entry => entry.sizeOfRawData.toNat) = some 512 := by
  rw [table_sections]
  simp [textDescription_paddedRawData_length]

example : table.headers.optionalHeader.imageFields.sizeOfHeaders.toNat =
    512 := by
  change (BitVec.ofNat 32 512).toNat = 512
  decide

example : bytes.length = 1024 := by
  unfold bytes ImageDescription.bytes
  simp only [Vec.length_append, Vec.length_replicate,
    length_writeImageSectionTable]
  rw [description_firstRawDataOffset, description_fileAlignment,
    description_sections_toList, writeImageSectionDescriptionList_singleton,
    textDescription_paddedRawData_length]
  decide

example : writeImageDescription description = .ok bytes := by
  unfold writeImageDescription
  rw [dif_pos description_writable]
  rfl

end Grass.Tests.Artifact.PE.ImageWriter
