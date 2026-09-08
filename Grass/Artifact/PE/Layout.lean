import Grass.Artifact.COFF.Layout
import Grass.Artifact.PE.ImageSectionTable

/-!
# PE32+ declared image spans

This module lifts the section-table pointer and size fields into overflow-free
PE image spans. It reuses the generic span algebra and COFF section field
representation, but accounts for the PE signature and enforces the image-only
absence of COFF relocation and line-number regions.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Artifact.COFF Grass.Std.Logical

/-- The complete headers and section table form one leading image span. -/
def ImageSectionTable.headerSpan (table : ImageSectionTable) : ByteSpan where
  offset := 0
  length := 264 +
    40 * table.headers.headerPrefix.fileHeader.numberOfSections.toNat

/-- Raw-data spans declared by all image sections in table order. -/
def imageSectionRawSpans (table : ImageSectionTable) : List ByteSpan :=
  table.sections.toList.map SectionHeader.rawDataSpan

/-- Every independently placed span declared by a canonical PE image table. -/
def declaredImageSpans (table : ImageSectionTable) : List ByteSpan :=
  table.headerSpan :: imageSectionRawSpans table

/-- Image section headers use only the raw-data pointer and zero every COFF
relocation and line-number pointer/count field. -/
def imageSectionPointersCoherent (sectionHeader : SectionHeader) :
    Prop :=
  sectionHeader.rawDataSpan.PointerCoherent ∧
  sectionHeader.pointerToRelocations.toNat = 0 ∧
  sectionHeader.numberOfRelocations.toNat = 0 ∧
  sectionHeader.pointerToLineNumbers.toNat = 0 ∧
  sectionHeader.numberOfLineNumbers.toNat = 0

instance (sectionHeader : SectionHeader) :
    Decidable (imageSectionPointersCoherent sectionHeader) := by
  unfold imageSectionPointersCoherent
  infer_instance

/-- Structural validity of all file-addressed regions in a PE image. -/
def DeclaredImageLayoutValid (table : ImageSectionTable)
    (fileLength : Nat) : Prop :=
  (∀ sectionHeader ∈ table.sections.toList,
    imageSectionPointersCoherent sectionHeader) ∧
  (∀ span ∈ declaredImageSpans table, span.Fits fileLength) ∧
  (declaredImageSpans table).Pairwise ByteSpan.Disjoint

instance (table : ImageSectionTable) (fileLength : Nat) :
    Decidable (DeclaredImageLayoutValid table fileLength) := by
  unfold DeclaredImageLayoutValid
  infer_instance

/-- `ImageSectionTable.headerSpan_endExclusive` computes the first possible
byte after the serialized headers and section table. -/
@[simp] theorem ImageSectionTable.headerSpan_endExclusive
    (table : ImageSectionTable) :
    table.headerSpan.endExclusive =
      264 + 40 *
        table.headers.headerPrefix.fileHeader.numberOfSections.toNat := by
  simp [ImageSectionTable.headerSpan, ByteSpan.endExclusive]

/-- The PE header span length agrees with the concrete section-table writer. -/
theorem ImageSectionTable.headerSpan_length_write
    (table : ImageSectionTable) :
    table.headerSpan.length = (writeImageSectionTable table).length := by
  simp [ImageSectionTable.headerSpan]

/-- A valid declared layout places the complete header span inside the file. -/
theorem DeclaredImageLayoutValid.header_fits
    {table : ImageSectionTable} {fileLength : Nat}
    (valid : DeclaredImageLayoutValid table fileLength) :
    table.headerSpan.Fits fileLength := by
  exact valid.2.1 table.headerSpan (by
    simp [declaredImageSpans])

/-- Every section in a valid layout has image-coherent pointer fields. -/
theorem DeclaredImageLayoutValid.section_pointers
    {table : ImageSectionTable} {fileLength : Nat}
    (valid : DeclaredImageLayoutValid table fileLength)
    {sectionHeader : SectionHeader}
    (member : sectionHeader ∈ table.sections.toList) :
    imageSectionPointersCoherent sectionHeader :=
  valid.1 sectionHeader member

/-- Every declared section raw-data span in a valid layout fits the file. -/
theorem DeclaredImageLayoutValid.raw_data_fits
    {table : ImageSectionTable} {fileLength : Nat}
    (valid : DeclaredImageLayoutValid table fileLength)
    {sectionHeader : SectionHeader}
    (member : sectionHeader ∈ table.sections.toList) :
    sectionHeader.rawDataSpan.Fits fileLength := by
  apply valid.2.1
  simp only [declaredImageSpans, List.mem_cons]
  right
  simp only [imageSectionRawSpans, List.mem_map]
  exact ⟨sectionHeader, member, rfl⟩

/-- Validity exposes pairwise non-overlap of every declared PE image span. -/
theorem DeclaredImageLayoutValid.spans_pairwise
    {table : ImageSectionTable} {fileLength : Nat}
    (valid : DeclaredImageLayoutValid table fileLength) :
    (declaredImageSpans table).Pairwise ByteSpan.Disjoint :=
  valid.2.2

end Grass.Artifact.PE
