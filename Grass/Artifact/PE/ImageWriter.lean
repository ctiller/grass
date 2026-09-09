import Grass.Artifact.PE.HeaderPrefix
import Grass.Artifact.PE.OptionalHeader
import Grass.Artifact.PE.SectionTable

/-!
# Canonical PE32+ image writer

`writeImage` consumes one checked layout. Requested imports are
materialized into a generated `.idata` section before placement and header
serialization.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical

/-- Serialize all typed headers before file-alignment padding. -/
def writeUnpaddedHeaders (layout : ImageLayout) : Std.Logical.ByteArray :=
  writeHeaderPrefix (BitVec.ofNat 16 layout.placed.length) ++
    writeOptionalHeader layout ++ writeSectionTable layout.placed

/-- The typed header serialization ends exactly at the absolute NT-header end. -/
@[simp] theorem length_writeUnpaddedHeaders (layout : ImageLayout) :
    (writeUnpaddedHeaders layout).length =
      (ntHeadersSpan canonicalPeOffset layout.placed.length).endOffset := by
  simp [writeUnpaddedHeaders, ntHeadersSpan, ntHeadersSize, FileSpan.endOffset]
  omega

/-- Append header padding up to the first raw section offset. -/
def writeAlignedHeaders (layout : ImageLayout) : Std.Logical.ByteArray :=
  let headers := writeUnpaddedHeaders layout
  let target := firstRawOffset canonicalPeOffset layout.placed.length canonicalFileAlignment
  headers ++ Vec.replicate (target - headers.length) 0

/-- `writeAlignedHeaders` has exactly the offset assigned to the first raw
section. -/
@[simp] theorem length_writeAlignedHeaders (layout : ImageLayout) :
    (writeAlignedHeaders layout).length =
      firstRawOffset canonicalPeOffset layout.placed.length canonicalFileAlignment := by
  simp only [writeAlignedHeaders, Vec.length_append, Vec.length_replicate]
  rw [length_writeUnpaddedHeaders]
  have bounded := ntHeaders_end_le_firstRawOffset
    canonicalPeOffset layout.placed.length canonicalFileAlignment
  omega

/-- Serialize aligned section contents in placement order. -/
def writePlacedContentsList : List PlacedSection → Std.Logical.ByteArray
  | [] => Vec.empty
  | placed :: tail => placed.paddedContents ++ writePlacedContentsList tail

/-- Sum the declared raw extents of placed sections. -/
def totalRawSize : List PlacedSection → Nat
  | [] => 0
  | placed :: tail => placed.rawSpan.size + totalRawSize tail

/-- Every list produced by placement serializes to its exact total raw extent. -/
theorem length_writePlacedContentsList
    (virtualCursor rawCursor sectionAlignment fileAlignment : Nat)
    (sections : List RawSection) :
    (writePlacedContentsList
      (placeSectionsFrom virtualCursor rawCursor sectionAlignment fileAlignment sections)).length =
    totalRawSize
      (placeSectionsFrom virtualCursor rawCursor sectionAlignment fileAlignment sections) := by
  induction sections generalizing virtualCursor rawCursor with
  | nil => simp [placeSectionsFrom, writePlacedContentsList, totalRawSize]
  | cons source tail ih =>
      simp only [placeSectionsFrom, writePlacedContentsList, totalRawSize, Vec.length_append]
      rw [PlacedSection.length_paddedContents]
      · rw [ih]
      · exact le_alignUp _ _

/-- Emit a complete canonical PE32+ image from the instruction-independent
adapter input. -/
def writeImage (plan : ImagePlan) : Std.Logical.ByteArray :=
  writeAlignedHeaders plan.layout ++ writePlacedContentsList plan.layout.placed.toList

/-- Successful complete-image writing has the exact aligned-header plus raw
payload extent. -/
theorem length_writeImage (plan : ImagePlan) :
    (writeImage plan).length =
      firstRawOffset canonicalPeOffset plan.layout.placed.length canonicalFileAlignment +
        totalRawSize plan.layout.placed.toList := by
  unfold writeImage
  simp only [Vec.length_append, length_writeAlignedHeaders]
  rw [plan.layout.placed_eq]
  simp only [placeImageSections, Vec.toList_fromList]
  congr 1
  exact length_writePlacedContentsList _ _ _ _ _

end Grass.Artifact.PE
