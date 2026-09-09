import Grass.Artifact.PE.ImageReader

/-! # Exact complete-image reader/writer recovery -/

namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical Grass.Artifact.Binary

/-- Expected full raw contents of a placed section. -/
def PlacedSection.expectedContents (placed : PlacedSection) : ParsedSectionContents :=
  ⟨placed.expectedSectionHeader, placed.paddedContents⟩

/-- Declared contiguous raw spans recover all bytes with an exact suffix. -/
theorem readSectionContents_write_append (sections : List PlacedSection)
    (cursor : Nat) (suffix : Std.Logical.ByteArray)
    (contiguous : RawContiguous cursor sections)
    (fits : ∀ s ∈ sections, s.rawSpan.start < 2 ^ 32 ∧ s.rawSpan.size < 2 ^ 32)
    (contains : ∀ s ∈ sections, s.source.contents.length ≤ s.rawSpan.size) :
    readSectionContents (sections.map PlacedSection.expectedSectionHeader) cursor
      (writePlacedContentsList sections ++ suffix) =
      .done (sections.map PlacedSection.expectedContents) suffix := by
  induction sections generalizing cursor with
  | nil => simp [readSectionContents, writePlacedContentsList]
  | cons head tail ih =>
      have headFits := fits head (by simp)
      have headContains := contains head (by simp)
      have start : head.expectedSectionHeader.rawOffset.toNat = cursor := by
        simpa [PlacedSection.expectedSectionHeader, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt headFits.1] using contiguous.1
      have size : head.expectedSectionHeader.rawSize.toNat = head.rawSpan.size := by
        simp [PlacedSection.expectedSectionHeader, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt headFits.2]
      simp only [List.map_cons, writePlacedContentsList, Vec.append_assoc,
        readSectionContents, start, ↓reduceIte, size]
      rw [takeExact_append (head.length_paddedContents headContains)]
      simp only [continueRead]
      have next : RawContiguous (cursor + head.rawSpan.size) tail := by
        simpa [FileSpan.endOffset, contiguous.1] using contiguous.2
      rw [ih (cursor + head.rawSpan.size) next
        (fun s member => fits s (by simp [member]))
        (fun s member => contains s (by simp [member]))]
      rfl

/-- The exact decoded record expected from a checked image plan. -/
def ImagePlan.expectedImage (plan : ImagePlan) : ParsedImage where
  header := expectedHeaderPrefix (BitVec.ofNat 16 plan.layout.placed.length)
  optional := expectedOptionalHeader plan.layout
  headerPadding := Vec.replicate
    (firstRawOffset canonicalPeOffset plan.layout.placed.length canonicalFileAlignment -
      (ntHeadersSpan canonicalPeOffset plan.layout.placed.length).endOffset) 0
  sections := plan.layout.placed.toList.map PlacedSection.expectedContents

/-- The selected writer's identifying fields meet the reader's container profile. -/
theorem supportedImageHeader_expected (layout : ImageLayout) :
    supportedImageHeader (expectedHeaderPrefix (BitVec.ofNat 16 layout.placed.length))
      (expectedOptionalHeader layout) = true := by
  simp [supportedImageHeader, expectedHeaderPrefix, expectedOptionalHeader,
    canonicalPeOffset]

/-- Every checked image is recovered exactly, including all header fields,
padding, section identities and raw payload bytes. -/
theorem readImage_writeImage (plan : ImagePlan) :
    readImage (writeImage plan) = .done plan.expectedImage Vec.empty := by
  have countEq : plan.layout.placed.length = plan.layout.materialized.sections.length := by
    rw [plan.layout.placed_eq]
    exact placeImageSections_length _
  have countFits : plan.layout.placed.length < 2 ^ 16 := by
    rw [countEq]
    exact plan.writable.sectionCountFits
  have countValue : (BitVec.ofNat 16 plan.layout.placed.length).toNat =
      plan.layout.placed.length := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countFits]
  have headerValue : (expectedOptionalHeader plan.layout).sizeOfHeaders.toNat =
      firstRawOffset canonicalPeOffset plan.layout.placed.length canonicalFileAlignment := by
    simp [expectedOptionalHeader, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt plan.writable.headerSizeFits]
  have contiguous : RawContiguous
      (firstRawOffset canonicalPeOffset plan.layout.placed.length canonicalFileAlignment)
      plan.layout.placed.toList := by
    rw [countEq]
    exact plan.rawContiguous
  have contains : ∀ s ∈ plan.layout.placed.toList,
      s.source.contents.length ≤ s.rawSpan.size := by
    rw [plan.layout.placed_eq]
    exact placed_rawSize_ge _ _ _ _ _
  have rawReads := readSectionContents_write_append plan.layout.placed.toList
    (firstRawOffset canonicalPeOffset plan.layout.placed.length canonicalFileAlignment)
    Vec.empty contiguous
    (fun s member => ⟨(plan.writable.placementFields member).2.2.2.1,
      (plan.writable.placementFields member).2.2.2.2.1⟩) contains
  simp only [Vec.append_empty] at rawReads
  unfold writeImage writeAlignedHeaders writeUnpaddedHeaders
  simp only [Vec.append_assoc, readImage, readHeaderPrefix_write_append, continueRead,
    readOptionalHeader_write_append,
    expectedHeaderPrefix, countValue]
  change continueRead (readSectionHeaders plan.layout.placed.toList.length
    (writeSectionTableList plan.layout.placed.toList ++ _)) _ = _
  rw [readSectionHeaders_write_append]
  simp only [continueRead, headerValue]
  have bounded := ntHeaders_end_le_firstRawOffset canonicalPeOffset
    plan.layout.placed.length canonicalFileAlignment
  have endEq : canonicalPeOffset + peSignatureSize + coffHeaderSize +
      optionalHeader64Size + sectionHeaderSize * plan.layout.placed.length =
      (ntHeadersSpan canonicalPeOffset plan.layout.placed.length).endOffset := by
    simp [ntHeadersSpan, ntHeadersSize, FileSpan.endOffset, Nat.add_assoc]
  rw [endEq]
  rw [if_pos bounded]
  have emittedLength : (writeHeaderPrefix (BitVec.ofNat 16 plan.layout.placed.length) ++
      (writeOptionalHeader plan.layout ++ writeSectionTable plan.layout.placed)).length =
      (ntHeadersSpan canonicalPeOffset plan.layout.placed.length).endOffset := by
    simpa [writeUnpaddedHeaders, Vec.append_assoc] using length_writeUnpaddedHeaders plan.layout
  rw [emittedLength]
  rw [takeExact_append (Vec.length_replicate _ _)]
  simp only [rawReads, Vec.length_empty, ↓reduceIte]
  rfl

end Grass.Artifact.PE
