import Grass.Artifact.PE.Layout

/-!
# Parsed PE32+ images

The image reader combines canonical headers, their count-coupled section table,
and independently addressed raw section payloads. It validates all declared
file spans before returning a value; instruction and loader semantics remain
outside this binary container layer.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

/-- The independently addressed raw-data region belonging to one PE section. -/
structure ImageSectionContents where
  header : SectionHeader
  rawData : SectionRawData header
deriving DecidableEq, Repr

/-- Read one section payload from its absolute file offset. -/
def readImageSectionContents (sectionHeader : SectionHeader)
    (file : Std.Logical.ByteArray) : ParseResult ImageSectionContents :=
  if _fits : sectionHeader.rawDataSpan.endExclusive ≤ file.length then
    match readSectionRawData sectionHeader
        (file.drop sectionHeader.rawDataSpan.offset) with
    | .done rawData _ => .done ⟨sectionHeader, rawData⟩ Vec.empty
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else
    .needMore (some
      (sectionHeader.rawDataSpan.endExclusive - file.length))

/-- A file shorter than a section's declared end reports the exact deficit. -/
theorem readImageSectionContents_short (sectionHeader : SectionHeader)
    {file : Std.Logical.ByteArray}
    (short : file.length < sectionHeader.rawDataSpan.endExclusive) :
    readImageSectionContents sectionHeader file =
      .needMore (some
        (sectionHeader.rawDataSpan.endExclusive - file.length)) := by
  simp [readImageSectionContents, Nat.not_le.mpr short]

/-- An exact payload at the declared offset composes into a successful read. -/
theorem readImageSectionContents_of_region
    (contents : ImageSectionContents)
    (file suffix : Std.Logical.ByteArray)
    (fits : contents.header.rawDataSpan.endExclusive ≤ file.length)
    (regionAt : file.drop contents.header.rawDataSpan.offset =
      writeSectionRawData contents.rawData ++ suffix) :
    readImageSectionContents contents.header file =
      .done contents Vec.empty := by
  rcases contents with ⟨header, rawData⟩
  simp only [readImageSectionContents, fits, dite_true]
  rw [regionAt, readSectionRawData_write_append]

/-- Read addressed raw payloads for every section header in source order. -/
def readImageSectionContentsList :
    List SectionHeader → Std.Logical.ByteArray →
      ParseResult (List ImageSectionContents)
  | [], _ => .done [] Vec.empty
  | header :: headers, file =>
    match readImageSectionContents header file with
    | .done content _ =>
      match readImageSectionContentsList headers file with
      | .done contents _ => .done (content :: contents) Vec.empty
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- Exact reads for each payload compose into an exact ordered list read. -/
theorem readImageSectionContentsList_of_reads
    (contents : List ImageSectionContents)
    (file : Std.Logical.ByteArray)
    (reads : ∀ content ∈ contents,
      readImageSectionContents content.header file =
        .done content Vec.empty) :
    readImageSectionContentsList
      (contents.map ImageSectionContents.header) file =
      .done contents Vec.empty := by
  induction contents with
  | nil => rfl
  | cons content contents ih =>
      simp only [List.map_cons, readImageSectionContentsList]
      rw [reads content (by simp)]
      rw [ih (fun tail member => reads tail (by simp [member]))]

/-- Successful payload collection retains exactly the supplied headers. -/
theorem readImageSectionContentsList_headers {headers file contents rest}
    (success : readImageSectionContentsList headers file =
      .done contents rest) :
    contents.map ImageSectionContents.header = headers := by
  induction headers generalizing contents rest with
  | nil =>
      simp only [readImageSectionContentsList] at success
      injection success with contentsEq
      rw [← contentsEq]
      rfl
  | cons header headers ih =>
      simp only [readImageSectionContentsList] at success
      split at success <;> try contradiction
      next content ignored parsedContent =>
        split at success <;> try contradiction
        next tail ignoredTail parsedTail =>
          injection success with contentsEq
          rw [← contentsEq]
          change content.header :: tail.map ImageSectionContents.header =
            header :: headers
          have headerEq : content.header = header := by
            simp only [readImageSectionContents] at parsedContent
            split at parsedContent <;> try contradiction
            split at parsedContent <;> try contradiction
            next rawData rawRest =>
              injection parsedContent with valueEq
              rw [← valueEq]
          rw [headerEq, ih parsedTail]

/-- A complete PE32+ image with checked section identity and file layout. -/
structure Image where
  bytes : Std.Logical.ByteArray
  table : ImageSectionTable
  contents : Vec ImageSectionContents
  contentHeaders : contents.map ImageSectionContents.header = table.sections
  layoutValid : DeclaredImageLayoutValid table bytes.length
deriving DecidableEq, Repr

/-- Parse and validate one complete canonical PE32+ image byte array. -/
def readImage (file : Std.Logical.ByteArray) : ParseResult Image :=
  match readImageSectionTable file with
  | .done table _ =>
    match readImageSectionContentsList table.sections.toList file with
    | .done contentList _ =>
      let contents := Vec.fromList contentList
      if headers :
          contents.map ImageSectionContents.header = table.sections then
        if valid : DeclaredImageLayoutValid table file.length then
          .done {
            bytes := file
            table := table
            contents := contents
            contentHeaders := headers
            layoutValid := valid } Vec.empty
        else
          .invalid (.malformed
            "PE32+ image spans overlap or exceed the file")
      else
        .invalid (.malformed "PE32+ section content headers mismatch")
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

end Grass.Artifact.PE
