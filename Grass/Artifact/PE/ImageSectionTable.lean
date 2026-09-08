import Grass.Artifact.COFF.SectionTable
import Grass.Artifact.PE.ImageHeaders

/-!
# PE32+ image section table

This module couples canonical PE32+ image headers to exactly the number of
40-byte COFF section entries declared by their embedded file header. Section
contents and layout validity remain later artifact layers.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

/-- Canonical image headers followed by their exactly declared section entries. -/
structure ImageSectionTable where
  headers : ImageHeaders
  sections : Vec SectionHeader
  sectionCount :
    sections.length = headers.headerPrefix.fileHeader.numberOfSections.toNat
deriving DecidableEq, Repr

/-- Grammar product before the declared section count is promoted. -/
abbrev ImageSectionTableProduct := ImageHeaders × Vec SectionHeader

/-- Product refined by the embedded COFF header's section count. -/
abbrev CheckedImageSectionTable :=
  {table : ImageSectionTableProduct //
    table.2.length =
      table.1.headerPrefix.fileHeader.numberOfSections.toNat}

/-- Restore a named image section table from its checked grammar product. -/
def ImageSectionTable.ofChecked (table : CheckedImageSectionTable) :
    ImageSectionTable :=
  ⟨table.1.1, table.1.2, table.2⟩

/-- Forget field labels while retaining the exact section-count proof. -/
def ImageSectionTable.toChecked (table : ImageSectionTable) :
    CheckedImageSectionTable :=
  ⟨(table.headers, table.sections), table.sectionCount⟩

/-- Named image section tables and checked products are totally isomorphic. -/
def imageSectionTableIsomorphism :
    Isomorphism CheckedImageSectionTable ImageSectionTable where
  forward := ImageSectionTable.ofChecked
  backward := ImageSectionTable.toChecked
  backward_forward := by
    intro table
    rcases table with ⟨⟨headers, sections⟩, count⟩
    rfl
  forward_backward := by
    intro table
    rcases table with ⟨headers, sections, count⟩
    rfl

/-- Headers followed by the number of sections declared in their COFF fields. -/
def rawImageSectionTableFormat : Format ImageSectionTableProduct :=
  .seq imageHeadersFormat fun headers =>
    .repeat headers.headerPrefix.fileHeader.numberOfSections.toNat
      sectionHeaderFormat

/-- Promote the declared section count into the grammar result type. -/
def checkedImageSectionTableFormat : Format CheckedImageSectionTable :=
  rawImageSectionTableFormat.refineValue fun table =>
    table.2.length =
      table.1.headerPrefix.fileHeader.numberOfSections.toNat

/-- Typed grammar of canonical image headers and their section table. -/
def imageSectionTableFormat : Format ImageSectionTable :=
  checkedImageSectionTableFormat.iso imageSectionTableIsomorphism

/-- Parse image headers and exactly their declared number of section entries. -/
def readImageSectionTable (input : Std.Logical.ByteArray) :
    ParseResult ImageSectionTable :=
  match readImageHeaders input with
  | .done headers afterHeaders =>
    let count := headers.headerPrefix.fileHeader.numberOfSections.toNat
    match readSectionHeaders count afterHeaders with
    | .done sections rest =>
      if sectionCount : sections.length = count then
        .done ⟨headers, sections, sectionCount⟩ rest
      else
        .invalid (.malformed "PE32+ section-table count mismatch")
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Serialize image headers followed by section entries in declared order. -/
def writeImageSectionTable (table : ImageSectionTable) :
    Std.Logical.ByteArray :=
  writeImageHeaders table.headers ++ writeSectionHeaders table.sections

/-- The serialized size is 264 bytes plus 40 per declared section. -/
@[simp] theorem length_writeImageSectionTable (table : ImageSectionTable) :
    (writeImageSectionTable table).length =
      264 + 40 * table.headers.headerPrefix.fileHeader.numberOfSections.toNat := by
  simp [writeImageSectionTable, table.sectionCount]

/-- `readImageSectionTable_write_append` states that a canonical section table
round-trips while preserving an arbitrary suffix. -/
@[simp] theorem readImageSectionTable_write_append
    (table : ImageSectionTable) (rest : Std.Logical.ByteArray) :
    readImageSectionTable (writeImageSectionTable table ++ rest) =
      .done table rest := by
  rcases table with ⟨headers, sections, count⟩
  simp only [readImageSectionTable, writeImageSectionTable, Vec.append_assoc,
    readImageHeaders_write_append]
  have parsed : readSectionHeaders
      headers.headerPrefix.fileHeader.numberOfSections.toNat
      (writeSectionHeaders sections ++ rest) = .done sections rest := by
    simpa only [← count] using
      readSectionHeaders_writeSectionHeaders_append sections rest
  rw [parsed]
  simp only [count, ↓reduceDIte]

/-- Whole-input canonical image-section-table round trip. -/
@[simp] theorem readImageSectionTable_write (table : ImageSectionTable) :
    readImageSectionTable (writeImageSectionTable table) =
      .done table Vec.empty := by
  simpa using readImageSectionTable_write_append table Vec.empty

/-- Every canonical image section table derives from its dependent grammar. -/
theorem writeImageSectionTable_derives (table : ImageSectionTable) :
    Derives imageSectionTableFormat (writeImageSectionTable table)
      table Vec.empty := by
  rcases table with ⟨headers, sections, count⟩
  unfold imageSectionTableFormat
  refine @Derives.iso CheckedImageSectionTable ImageSectionTable
    checkedImageSectionTableFormat imageSectionTableIsomorphism _ Vec.empty
    ⟨(headers, sections), count⟩ ?_
  unfold checkedImageSectionTableFormat
  apply Derives.lift
  unfold rawImageSectionTableFormat writeImageSectionTable
  exact Derives.seqAppend (writeImageHeaders_derives headers)
    (by simpa only [count] using writeSectionHeaders_derives sections)

end Grass.Artifact.PE
