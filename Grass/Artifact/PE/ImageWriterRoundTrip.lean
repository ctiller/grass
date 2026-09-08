import Grass.Artifact.PE.ImageWriter

/-!
# Canonical PE32+ image-writer correspondence

This module proves that layouts synthesized by `ImageDescription.bytes` satisfy
the independent `DeclaredImageLayoutValid` checker and prepares the exact
dependent section contents used by the image-reader round trip.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

/-- Total padded payload width for a list of image-section descriptions. -/
def imageSectionDescriptionListLength (alignment : Nat) :
    List ImageSectionDescription → Nat
  | [] => 0
  | description :: descriptions =>
    alignUp description.rawData.length alignment +
      imageSectionDescriptionListLength alignment descriptions

/-- The recursive payload writer has the declared total padded width. -/
@[simp] theorem length_writeImageSectionDescriptionList (alignment : Nat)
    (descriptions : List ImageSectionDescription) :
    (writeImageSectionDescriptionList alignment descriptions).length =
      imageSectionDescriptionListLength alignment descriptions := by
  induction descriptions with
  | nil => rfl
  | cons description descriptions ih =>
      simp [writeImageSectionDescriptionList,
        imageSectionDescriptionListLength, ih,
        ImageSectionDescription.paddedRawData]

/-- The layout cursor ends after exactly the padded payload widths. -/
theorem layoutImageSectionList_end (alignment offset : Nat)
    (descriptions : List ImageSectionDescription) :
    (layoutImageSectionList alignment offset descriptions).2 =
      offset + imageSectionDescriptionListLength alignment descriptions := by
  induction descriptions generalizing offset with
  | nil => simp [layoutImageSectionList, imageSectionDescriptionListLength]
  | cons description descriptions ih =>
      simp only [layoutImageSectionList, imageSectionDescriptionListLength]
      rw [ih]
      omega

/-- The placement scan exposes the head and recursive representability facts. -/
theorem imageSectionPlacementsFit_cons_iff
    (alignment offset : Nat) (description : ImageSectionDescription)
    (descriptions : List ImageSectionDescription) :
    imageSectionPlacementsFit alignment offset
        (description :: descriptions) = true ↔
      alignUp description.rawData.length alignment < 2 ^ 32 ∧
      (alignUp description.rawData.length alignment = 0 ∨
        offset + alignUp description.rawData.length alignment < 2 ^ 32) ∧
      imageSectionPlacementsFit alignment
        (offset + alignUp description.rawData.length alignment)
        descriptions = true := by
  simp [imageSectionPlacementsFit, and_assoc]

/-- Every header emitted by a writable placement scan has coherent PE fields. -/
theorem layoutImageSectionList_pointersCoherent
    (alignment offset : Nat) (descriptions : List ImageSectionDescription)
    (offsetPositive : 0 < offset)
    (placements : imageSectionPlacementsFit alignment offset descriptions = true) :
    ∀ header ∈ (layoutImageSectionList alignment offset descriptions).1,
      imageSectionPointersCoherent header := by
  induction descriptions generalizing offset with
  | nil => simp [layoutImageSectionList]
  | cons description descriptions ih =>
      have facts := (imageSectionPlacementsFit_cons_iff alignment offset
        description descriptions).mp placements
      have lengthNonnegative : 0 ≤ alignUp description.rawData.length alignment :=
        Nat.zero_le _
      intro header member
      simp only [layoutImageSectionList, List.mem_cons] at member
      rcases member with rfl | tailMember
      · apply description.headerAt_imageSectionPointersCoherent alignment offset
          offsetPositive facts.1 facts.2.1
      · exact ih (offset + alignUp description.rawData.length alignment)
          (by omega) facts.2.2 header tailMember

/-- Every synthesized raw-data span is empty at zero or lies inside the
contiguous payload interval assigned to its description list. -/
theorem layoutImageSectionList_rawSpan_bounds
    (alignment offset : Nat) (descriptions : List ImageSectionDescription)
    (placements : imageSectionPlacementsFit alignment offset descriptions = true)
    {span : ByteSpan}
    (member : span ∈ (layoutImageSectionList alignment offset descriptions).1.map
      SectionHeader.rawDataSpan) :
    (span.offset = 0 ∧ span.length = 0) ∨
      (offset ≤ span.offset ∧ span.endExclusive ≤
        offset + imageSectionDescriptionListLength alignment descriptions) := by
  induction descriptions generalizing offset with
  | nil => simp [layoutImageSectionList] at member
  | cons description descriptions ih =>
      let length := alignUp description.rawData.length alignment
      have facts := (imageSectionPlacementsFit_cons_iff alignment offset
        description descriptions).mp placements
      simp only [layoutImageSectionList, List.map_cons, List.mem_cons] at member
      rcases member with rfl | tailMember
      · rw [description.headerAt_rawDataSpan alignment offset facts.1 facts.2.1]
        split
        next empty => exact Or.inl ⟨rfl, rfl⟩
        next nonempty =>
          right
          simp only [ByteSpan.endExclusive]
          unfold imageSectionDescriptionListLength
          constructor <;> omega
      · rcases ih (offset + length) facts.2.2 tailMember with empty | bounded
        · exact Or.inl empty
        · right
          unfold imageSectionDescriptionListLength
          constructor <;> omega

/-- Canonically synthesized raw-data spans are pairwise disjoint. -/
theorem layoutImageSectionList_rawSpans_pairwise
    (alignment offset : Nat) (descriptions : List ImageSectionDescription)
    (placements : imageSectionPlacementsFit alignment offset descriptions = true) :
    ((layoutImageSectionList alignment offset descriptions).1.map
      SectionHeader.rawDataSpan).Pairwise ByteSpan.Disjoint := by
  induction descriptions generalizing offset with
  | nil => simp [layoutImageSectionList]
  | cons description descriptions ih =>
      let length := alignUp description.rawData.length alignment
      have facts := (imageSectionPlacementsFit_cons_iff alignment offset
        description descriptions).mp placements
      simp only [layoutImageSectionList, List.map_cons]
      apply List.Pairwise.cons
      · intro tailSpan tailMember
        have tailBound := layoutImageSectionList_rawSpan_bounds alignment
          (offset + length) descriptions facts.2.2 tailMember
        rw [description.headerAt_rawDataSpan alignment offset facts.1 facts.2.1]
        split
        next empty =>
          left
          simp [ByteSpan.endExclusive]
        next nonempty =>
          rcases tailBound with tailEmpty | tailBounded
          · right
            rcases tailEmpty with ⟨tailOffset, tailLength⟩
            simp [ByteSpan.endExclusive, tailOffset, tailLength]
          · left
            simp only [ByteSpan.endExclusive] at tailBounded ⊢
            exact tailBounded.1
      · exact ih (offset + length) facts.2.2

/-- The synthesized section table occupies the description's unaligned header
width exactly. -/
theorem ImageDescription.length_writeImageSectionTable
    (description : ImageDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    (writeImageSectionTable
      (description.imageSectionTable sectionCountFits)).length =
      description.unalignedHeaderSize := by
  rw [Grass.Artifact.PE.length_writeImageSectionTable]
  have count :
      (description.imageSectionTable sectionCountFits).headers.headerPrefix.fileHeader.numberOfSections.toNat =
        description.sections.length := by
    rw [← (description.imageSectionTable sectionCountFits).sectionCount]
    exact description.length_sectionLayout
  rw [count]
  rfl

/-- Canonical image bytes end at the final synthesized payload cursor. -/
theorem ImageDescription.length_bytes (description : ImageDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    (description.bytes sectionCountFits).length = description.sectionLayout.2 := by
  have headerLength := description.length_writeImageSectionTable sectionCountFits
  have headerLe :
      description.unalignedHeaderSize ≤ description.firstRawDataOffset := by
    exact le_alignUp description.unalignedHeaderSize description.fileAlignment
  unfold ImageDescription.bytes
  simp only [Vec.length_append, Vec.length_replicate,
    length_writeImageSectionDescriptionList]
  rw [headerLength]
  unfold ImageDescription.sectionLayout
  rw [layoutImageSectionList_end]
  change description.unalignedHeaderSize +
      (description.firstRawDataOffset - description.unalignedHeaderSize) +
      imageSectionDescriptionListLength description.fileAlignment
        description.sections.toList =
    description.firstRawDataOffset +
      imageSectionDescriptionListLength description.fileAlignment
        description.sections.toList
  omega

/-- The synthesized raw-span list is exactly the recursive layout span list. -/
theorem ImageDescription.imageSectionRawSpans_imageSectionTable
    (description : ImageDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    imageSectionRawSpans (description.imageSectionTable sectionCountFits) =
      (layoutImageSectionList description.fileAlignment
        description.firstRawDataOffset description.sections.toList).1.map
          SectionHeader.rawDataSpan := by
  rfl

/-- A writable image description's aligned header offset is positive. -/
theorem ImageDescription.firstRawDataOffset_pos
    (description : ImageDescription) : 0 < description.firstRawDataOffset := by
  have bounded := le_alignUp description.unalignedHeaderSize
    description.fileAlignment
  exact Nat.lt_of_lt_of_le (by
    unfold ImageDescription.unalignedHeaderSize
    omega) bounded

/-- Every writable image description synthesizes a coherent, bounded,
pairwise-disjoint declared image layout. -/
theorem ImageDescription.layoutValid (description : ImageDescription)
    (writable : description.Writable) :
    DeclaredImageLayoutValid
      (description.imageSectionTable writable.2.1)
      (description.bytes writable.2.1).length := by
  let table := description.imageSectionTable writable.2.1
  have pointers : ∀ header ∈ table.sections.toList,
      imageSectionPointersCoherent header := by
    simpa only [table, ImageDescription.imageSectionTable,
      ImageDescription.sectionLayout, Vec.toList_fromList] using
      layoutImageSectionList_pointersCoherent description.fileAlignment
        description.firstRawDataOffset description.sections.toList
        description.firstRawDataOffset_pos writable.2.2.2
  have rawBounds : ∀ span ∈ imageSectionRawSpans table,
      (span.offset = 0 ∧ span.length = 0) ∨
        (description.firstRawDataOffset ≤ span.offset ∧
          span.endExclusive ≤ description.sectionLayout.2) := by
    intro span member
    have bounded := layoutImageSectionList_rawSpan_bounds description.fileAlignment
      description.firstRawDataOffset description.sections.toList
      writable.2.2.2 (span := span) (by
        simpa only [table,
          description.imageSectionRawSpans_imageSectionTable writable.2.1] using member)
    simpa only [ImageDescription.sectionLayout, layoutImageSectionList_end] using
      bounded
  have rawPairwise : (imageSectionRawSpans table).Pairwise ByteSpan.Disjoint := by
    simpa only [table,
      description.imageSectionRawSpans_imageSectionTable writable.2.1] using
        layoutImageSectionList_rawSpans_pairwise description.fileAlignment
          description.firstRawDataOffset description.sections.toList
          writable.2.2.2
  have headerEnd : table.headerSpan.endExclusive =
      description.unalignedHeaderSize := by
    change 0 + table.headerSpan.length = description.unalignedHeaderSize
    rw [Nat.zero_add]
    rw [table.headerSpan_length_write]
    exact description.length_writeImageSectionTable writable.2.1
  have firstOffsetBound :
      description.unalignedHeaderSize ≤ description.firstRawDataOffset :=
    le_alignUp description.unalignedHeaderSize description.fileAlignment
  have fileLength : (description.bytes writable.2.1).length =
      description.sectionLayout.2 :=
    description.length_bytes writable.2.1
  refine ⟨pointers, ?_, ?_⟩
  · intro span member
    simp only [declaredImageSpans, List.mem_cons] at member
    rcases member with rfl | rawMember
    · unfold ByteSpan.Fits
      rw [headerEnd, fileLength]
      rw [ImageDescription.sectionLayout, layoutImageSectionList_end]
      omega
    · rcases rawBounds span rawMember with empty | bounded
      · unfold ByteSpan.Fits ByteSpan.endExclusive
        omega
      · unfold ByteSpan.Fits
        rw [fileLength]
        exact bounded.2
  · unfold declaredImageSpans
    apply List.Pairwise.cons
    · intro span member
      rcases rawBounds span member with empty | bounded
      · right
        unfold ByteSpan.endExclusive
        omega
      · left
        rw [headerEnd]
        exact Nat.le_trans firstOffsetBound bounded.1
    · exact rawPairwise

/-- Construct the dependent image-section contents corresponding to a
representable canonical layout. -/
def imageSectionContentsListAt (alignment offset : Nat)
    (descriptions : List ImageSectionDescription)
    (placements : imageSectionPlacementsFit alignment offset descriptions = true) :
    List ImageSectionContents :=
  match descriptions with
  | [] => []
  | description :: descriptions =>
    have facts := (imageSectionPlacementsFit_cons_iff alignment offset
      description descriptions).mp placements
    have payloadLength :
        (description.paddedRawData alignment).length =
          (description.headerAt alignment offset).sizeOfRawData.toNat := by
      symm
      apply description.headerAt_sizeOfRawData alignment offset
      simpa only [ImageSectionDescription.paddedRawData, length_padBytes] using
        facts.1
    { header := description.headerAt alignment offset
      rawData := ⟨description.paddedRawData alignment, payloadLength⟩ } ::
      imageSectionContentsListAt alignment
        (offset + alignUp description.rawData.length alignment)
        descriptions facts.2.2
termination_by descriptions.length

/-- Canonical dependent image contents retain the synthesized header list. -/
theorem imageSectionContentsListAt_headers (alignment offset : Nat)
    (descriptions : List ImageSectionDescription)
    (placements : imageSectionPlacementsFit alignment offset descriptions = true) :
    (imageSectionContentsListAt alignment offset descriptions placements).map
        ImageSectionContents.header =
      (layoutImageSectionList alignment offset descriptions).1 := by
  induction descriptions generalizing offset with
  | nil => simp [imageSectionContentsListAt, layoutImageSectionList]
  | cons description descriptions ih =>
      have facts := (imageSectionPlacementsFit_cons_iff alignment offset
        description descriptions).mp placements
      simp only [imageSectionContentsListAt, List.map_cons,
        layoutImageSectionList, List.cons.injEq, true_and]
      exact ih (offset + alignUp description.rawData.length alignment) facts.2.2

/-- Canonical dependent contents for all sections in an image description. -/
def ImageDescription.contents (description : ImageDescription)
    (writable : description.Writable) : Vec ImageSectionContents :=
  Vec.fromList (imageSectionContentsListAt description.fileAlignment
    description.firstRawDataOffset description.sections.toList writable.2.2.2)

/-- Description contents retain exactly the synthesized image-section table. -/
theorem ImageDescription.contents_headers (description : ImageDescription)
    (writable : description.Writable) :
    (description.contents writable).map ImageSectionContents.header =
      (description.imageSectionTable writable.2.1).sections := by
  apply Vec.toList_injective
  change (imageSectionContentsListAt description.fileAlignment
      description.firstRawDataOffset description.sections.toList
      writable.2.2.2).map ImageSectionContents.header =
    (layoutImageSectionList description.fileAlignment
      description.firstRawDataOffset description.sections.toList).1
  exact imageSectionContentsListAt_headers _ _ _ _

/-- A canonical payload list embedded after a prefix of the assigned length is
read back as the exact dependent image-section contents. -/
theorem readImageSectionContentsList_writeImageSectionDescriptionList
    (alignment offset : Nat) (descriptions : List ImageSectionDescription)
    (placements : imageSectionPlacementsFit alignment offset descriptions = true)
    (filePrefix suffix : Std.Logical.ByteArray)
    (prefixLength : filePrefix.length = offset) :
    readImageSectionContentsList
        (layoutImageSectionList alignment offset descriptions).1
        (filePrefix ++ writeImageSectionDescriptionList alignment descriptions ++
          suffix) =
      .done (imageSectionContentsListAt alignment offset descriptions placements)
        Vec.empty := by
  induction descriptions generalizing offset filePrefix with
  | nil => simp [layoutImageSectionList, writeImageSectionDescriptionList,
      imageSectionContentsListAt, readImageSectionContentsList]
  | cons description descriptions ih =>
      let length := alignUp description.rawData.length alignment
      let payload := description.paddedRawData alignment
      let header := description.headerAt alignment offset
      have facts := (imageSectionPlacementsFit_cons_iff alignment offset
        description descriptions).mp placements
      have payloadLength : payload.length = length := by
        simp [payload, length, ImageSectionDescription.paddedRawData]
      have headerSize : header.sizeOfRawData.toNat = payload.length := by
        apply description.headerAt_sizeOfRawData alignment offset
        rw [payloadLength]
        exact facts.1
      let rawData : SectionRawData header := ⟨payload, headerSize.symm⟩
      let content : ImageSectionContents := ⟨header, rawData⟩
      let tailBytes := writeImageSectionDescriptionList alignment descriptions
      let file := filePrefix ++ payload ++ tailBytes ++ suffix
      have headRead : readImageSectionContents header file =
          .done content Vec.empty := by
        by_cases empty : length = 0
        · have rawSpan : header.rawDataSpan = { offset := 0, length := 0 } := by
            dsimp only [header]
            rw [description.headerAt_rawDataSpan alignment offset facts.1 facts.2.1]
            simp [length, empty]
          have payloadEmpty : payload = Vec.empty :=
            (Vec.eq_empty_iff_length_eq_zero payload).mpr (by
              rw [payloadLength]
              exact empty)
          apply readImageSectionContents_of_region content file file
          · rw [rawSpan]
            simp [ByteSpan.endExclusive]
          · rw [rawSpan]
            change file = payload ++ file
            rw [payloadEmpty]
            simp
        · have rawSpan : header.rawDataSpan =
              { offset := offset, length := length } := by
            dsimp only [header]
            rw [description.headerAt_rawDataSpan alignment offset facts.1 facts.2.1]
            simp [length, empty]
          apply readImageSectionContents_of_region content file
            (tailBytes ++ suffix)
          · rw [rawSpan]
            simp only [ByteSpan.endExclusive]
            simp only [file, Vec.length_append, prefixLength, payloadLength]
            omega
          · rw [rawSpan]
            change file.drop offset = payload ++ (tailBytes ++ suffix)
            simp only [file, Vec.append_assoc]
            rw [← prefixLength, Vec.drop_append]
      have tailPrefixLength : (filePrefix ++ payload).length = offset + length := by
        simp [prefixLength, payloadLength]
      have tailRead := ih (offset + length) facts.2.2
        (filePrefix ++ payload) tailPrefixLength
      change readImageSectionContentsList
          (layoutImageSectionList alignment (offset + length) descriptions).1
          file =
        .done (imageSectionContentsListAt alignment (offset + length)
          descriptions facts.2.2) Vec.empty at tailRead
      simp only [layoutImageSectionList, readImageSectionContentsList]
      rw [show filePrefix ++
          writeImageSectionDescriptionList alignment
            (description :: descriptions) ++ suffix = file by
        simp [file, payload, tailBytes, writeImageSectionDescriptionList,
          Vec.append_assoc]]
      rw [headRead]
      simp only
      rw [tailRead]
      simp only
      change ParseResult.done (content :: imageSectionContentsListAt alignment
          (offset + length) descriptions facts.2.2) Vec.empty = _
      simp only [content, rawData, header, payload,
        imageSectionContentsListAt, length]

/-- The serialized header table plus alignment padding has exactly the assigned
first-payload offset. -/
theorem ImageDescription.length_headerPrefixBytes
    (description : ImageDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    (writeImageSectionTable (description.imageSectionTable sectionCountFits) ++
      Vec.replicate (description.firstRawDataOffset -
        (writeImageSectionTable
          (description.imageSectionTable sectionCountFits)).length) 0).length =
      description.firstRawDataOffset := by
  have headerLength := description.length_writeImageSectionTable sectionCountFits
  have headerLe :
      description.unalignedHeaderSize ≤ description.firstRawDataOffset :=
    le_alignUp description.unalignedHeaderSize description.fileAlignment
  simp only [Vec.length_append, Vec.length_replicate]
  rw [headerLength]
  omega

/-- The section-content phase reads canonical image bytes back into the exact
dependent contents synthesized from the description. -/
theorem ImageDescription.readImageSectionContentsList_bytes
    (description : ImageDescription) (writable : description.Writable) :
    readImageSectionContentsList
        (description.imageSectionTable writable.2.1).sections.toList
        (description.bytes writable.2.1) =
      .done (imageSectionContentsListAt description.fileAlignment
        description.firstRawDataOffset description.sections.toList
        writable.2.2.2) Vec.empty := by
  let headerPrefixBytes :=
    writeImageSectionTable (description.imageSectionTable writable.2.1) ++
      Vec.replicate (description.firstRawDataOffset -
        (writeImageSectionTable
          (description.imageSectionTable writable.2.1)).length) 0
  have prefixLength : headerPrefixBytes.length =
      description.firstRawDataOffset := by
    exact description.length_headerPrefixBytes writable.2.1
  have parsed :=
    readImageSectionContentsList_writeImageSectionDescriptionList
      description.fileAlignment description.firstRawDataOffset
      description.sections.toList writable.2.2.2 headerPrefixBytes Vec.empty
      prefixLength
  simpa only [headerPrefixBytes, ImageDescription.bytes,
    ImageDescription.imageSectionTable, ImageDescription.sectionLayout,
    Vec.toList_fromList, Vec.append_empty, Vec.append_assoc] using parsed

/-- Canonical bytes begin with the exact synthesized image section table. -/
theorem ImageDescription.readImageSectionTable_bytes
    (description : ImageDescription) (writable : description.Writable) :
    ∃ rest, readImageSectionTable (description.bytes writable.2.1) =
      .done (description.imageSectionTable writable.2.1) rest := by
  let rest := Vec.replicate (description.firstRawDataOffset -
      (writeImageSectionTable
        (description.imageSectionTable writable.2.1)).length) 0 ++
    writeImageSectionDescriptionList description.fileAlignment
      description.sections.toList
  refine ⟨rest, ?_⟩
  unfold ImageDescription.bytes
  simpa only [rest, Vec.append_assoc] using
    readImageSectionTable_write_append
      (description.imageSectionTable writable.2.1) rest

/-- The exact checked image value corresponding to a writable description. -/
def ImageDescription.image (description : ImageDescription)
    (writable : description.Writable) : Image where
  bytes := description.bytes writable.2.1
  table := description.imageSectionTable writable.2.1
  contents := description.contents writable
  contentHeaders := description.contents_headers writable
  layoutValid := description.layoutValid writable

/-- Canonical image bytes round-trip through the independent complete reader. -/
theorem ImageDescription.readImage_bytes (description : ImageDescription)
    (writable : description.Writable) :
    readImage (description.bytes writable.2.1) =
      .done (description.image writable) Vec.empty := by
  obtain ⟨rest, parsedTable⟩ :=
    description.readImageSectionTable_bytes writable
  have parsedContents :=
    description.readImageSectionContentsList_bytes writable
  have headers := description.contents_headers writable
  unfold ImageDescription.contents at headers
  have valid := description.layoutValid writable
  unfold readImage
  rw [parsedTable]
  simp only
  rw [parsedContents]
  simp only
  rw [dif_pos headers]
  rw [dif_pos valid]
  rfl

/-- Every successful canonical write is accepted by the complete image reader. -/
theorem readImage_writeImageDescription {description : ImageDescription}
    {bytes : Std.Logical.ByteArray}
    (success : writeImageDescription description = .ok bytes) :
    ∃ image, readImage bytes = .done image Vec.empty := by
  obtain ⟨writable, rfl⟩ := writeImageDescription_ok success
  exact ⟨description.image writable, description.readImage_bytes writable⟩

end Grass.Artifact.PE
