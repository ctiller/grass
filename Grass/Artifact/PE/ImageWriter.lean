import Grass.Artifact.PE.HeaderPrefix
import Grass.Artifact.PE.OptionalHeader
import Grass.Artifact.PE.SectionTable

/-!
# Canonical PE32+ image writer

`writeImage` is the first complete-file adapter consumed by x86 executable
fixtures. Its proof argument rejects narrowing overflow, and it currently
rejects nonempty imports rather than emitting a zero directory for a requested
import. The import-table builder will remove that explicit limitation.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical

/-- Current complete-writer precondition. Import requests fail closed until the
owned import-directory serializer is connected. -/
def ExecutableImageDescription.WriteReady
    (description : ExecutableImageDescription) : Prop :=
  description.Writable ∧ description.imports.length = 0

instance (description : ExecutableImageDescription) : Decidable description.WriteReady := by
  unfold ExecutableImageDescription.WriteReady
  infer_instance

/-- Serialize all typed headers before file-alignment padding. -/
def writeUnpaddedHeaders (description : ExecutableImageDescription)
    (placed : Vec PlacedSection) : Std.Logical.ByteArray :=
  writeHeaderPrefix (BitVec.ofNat 16 placed.length) ++
    writeOptionalHeader description placed ++ writeSectionTable placed

/-- The typed header serialization ends exactly at the absolute NT-header end. -/
@[simp] theorem length_writeUnpaddedHeaders (description : ExecutableImageDescription)
    (placed : Vec PlacedSection) :
    (writeUnpaddedHeaders description placed).length =
      (ntHeadersSpan canonicalPeOffset placed.length).endOffset := by
  simp [writeUnpaddedHeaders, ntHeadersSpan, ntHeadersSize, FileSpan.endOffset]
  omega

/-- Append header padding up to the first raw section offset. -/
def writeAlignedHeaders (description : ExecutableImageDescription)
    (placed : Vec PlacedSection) : Std.Logical.ByteArray :=
  let headers := writeUnpaddedHeaders description placed
  let target := firstRawOffset canonicalPeOffset placed.length canonicalFileAlignment
  headers ++ Vec.replicate (target - headers.length) 0

/-- `writeAlignedHeaders` has exactly the offset assigned to the first raw
section. -/
@[simp] theorem length_writeAlignedHeaders (description : ExecutableImageDescription)
    (placed : Vec PlacedSection) :
    (writeAlignedHeaders description placed).length =
      firstRawOffset canonicalPeOffset placed.length canonicalFileAlignment := by
  simp only [writeAlignedHeaders, Vec.length_append, Vec.length_replicate]
  rw [length_writeUnpaddedHeaders]
  have bounded := ntHeaders_end_le_firstRawOffset
    canonicalPeOffset placed.length canonicalFileAlignment
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

/-- Internal byte assembly after `WriteReady` has validated all narrowing and
the current empty-import limitation. -/
private def writeImageBytes (description : ExecutableImageDescription) :
    Std.Logical.ByteArray :=
  let placed := placeImageSections description
  writeAlignedHeaders description placed ++ writePlacedContentsList placed.toList

/-- Emit a complete canonical PE32+ image from the instruction-independent
adapter input. -/
def writeImage (description : ExecutableImageDescription)
    (_ready : description.WriteReady) : Std.Logical.ByteArray :=
  writeImageBytes description

/-- Successful complete-image writing has the exact aligned-header plus raw
payload extent. -/
theorem length_writeImage (description : ExecutableImageDescription)
    (ready : description.WriteReady) :
    (writeImage description ready).length =
      firstRawOffset canonicalPeOffset description.sections.length canonicalFileAlignment +
        totalRawSize (placeImageSections description).toList := by
  unfold writeImage writeImageBytes
  simp only [Vec.length_append, length_writeAlignedHeaders]
  rw [show description.sections.length = (placeImageSections description).length by simp]
  unfold placeImageSections
  rw [length_writePlacedContentsList]

end Grass.Artifact.PE
