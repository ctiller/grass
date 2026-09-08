import Grass.Artifact.COFF.Layout
import Grass.Artifact.COFF.SymbolValidation

/-!
# Parsed COFF relocatable objects

The whole-file reader combines the prefix table, independently addressed
section contents, and optional symbol/string tail. It validates every declared
span before returning a value and rejects optional-header bytes, which do not
belong to the modeled relocatable-object language.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- The three independently addressed byte regions belonging to one section. -/
structure SectionContents where
  header : SectionHeader
  rawData : SectionRawData header
  relocations : RelocationBlock header
  lineNumbers : LineNumberBlock header
deriving DecidableEq, Repr

/-- Optional symbol cells and their mandatory following string table. -/
inductive SymbolTail (header : Header) where
  | absent (pointerZero : header.pointerToSymbolTable.toNat = 0)
      (countZero : header.numberOfSymbols.toNat = 0)
  | present (pointerNonzero : header.pointerToSymbolTable.toNat ≠ 0)
      (symbols : AuxValidatedSymbolTable header) (strings : StringTable)
      (namesValid : symbols.NamesValid strings)
deriving DecidableEq, Repr

/-- Extract the optional parsed string table used by layout validation. -/
def SymbolTail.stringTable? {header : Header} :
    SymbolTail header → Option StringTable
  | .absent _ _ => none
  | .present _ _ strings _ => some strings

/-- A complete parsed relocatable object with checked cross-region layout. -/
structure Object where
  bytes : Std.Logical.ByteArray
  table : SectionTable
  contents : Vec SectionContents
  contentHeaders : contents.map SectionContents.header = table.sections
  symbols : SymbolTail table.header
  layoutValid : DeclaredObjectLayoutValid table.header table.sections
    symbols.stringTable? bytes.length
deriving DecidableEq, Repr

/-- Largest exclusive end among a section's three declared regions. -/
def SectionHeader.requiredContentEnd (sectionHeader : SectionHeader) : Nat :=
  max sectionHeader.rawDataSpan.endExclusive
    (max sectionHeader.relocationSpan.endExclusive
      sectionHeader.lineNumberSpan.endExclusive)

/-- Read all contents of one section from their declared file offsets. -/
def readSectionContents (sectionHeader : SectionHeader)
    (file : Std.Logical.ByteArray) : ParseResult SectionContents :=
  if _ : sectionHeader.requiredContentEnd ≤ file.length then
    match readSectionRawData sectionHeader
        (file.drop sectionHeader.rawDataSpan.offset) with
    | .done rawData _ =>
      match readRelocationBlock sectionHeader
          (file.drop sectionHeader.relocationSpan.offset) with
      | .done relocations _ =>
        match readLineNumberBlock sectionHeader
            (file.drop sectionHeader.lineNumberSpan.offset) with
        | .done lineNumbers _ =>
          .done { header := sectionHeader, rawData, relocations, lineNumbers }
            Vec.empty
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else
    .needMore (some (sectionHeader.requiredContentEnd - file.length))

/-- Exact independently addressed region serializations compose into a
successful section-content parse. Each suffix may include arbitrary following
object bytes because the three component readers preserve it. -/
theorem readSectionContents_of_regions (contents : SectionContents)
    (file rawSuffix relocationSuffix lineSuffix : Std.Logical.ByteArray)
    (enough : contents.header.requiredContentEnd ≤ file.length)
    (rawAt : file.drop contents.header.rawDataSpan.offset =
      writeSectionRawData contents.rawData ++ rawSuffix)
    (relocationsAt : file.drop contents.header.relocationSpan.offset =
      writeRelocationBlock contents.relocations ++ relocationSuffix)
    (linesAt : file.drop contents.header.lineNumberSpan.offset =
      writeLineNumberBlock contents.lineNumbers ++ lineSuffix) :
    readSectionContents contents.header file = .done contents Vec.empty := by
  rcases contents with ⟨header, rawData, relocations, lineNumbers⟩
  simp only [readSectionContents, enough, dite_true]
  rw [rawAt, readSectionRawData_write_append]
  rw [relocationsAt, readRelocationBlock_writeRelocationBlock_append]
  rw [linesAt, readLineNumberBlock_write_append]

/-- Read independently addressed contents for every header in source order. -/
def readSectionContentsList :
    List SectionHeader → Std.Logical.ByteArray → ParseResult (List SectionContents)
  | [], _ => .done [] Vec.empty
  | header :: headers, file =>
    match readSectionContents header file with
    | .done content _ =>
      match readSectionContentsList headers file with
      | .done contents _ => .done (content :: contents) Vec.empty
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- Exact reads for every content value compose into an exact list read in
source order. This is the list-level sequencing law for independently
addressed section regions. -/
theorem readSectionContentsList_of_reads (contents : List SectionContents)
    (file : Std.Logical.ByteArray)
    (reads : ∀ content ∈ contents,
      readSectionContents content.header file = .done content Vec.empty) :
    readSectionContentsList (contents.map SectionContents.header) file =
      .done contents Vec.empty := by
  induction contents with
  | nil => rfl
  | cons content contents ih =>
      simp only [List.map_cons, readSectionContentsList]
      rw [reads content (by simp)]
      rw [ih (fun tail member => reads tail (by simp [member]))]

/-- Successful section-content collection retains the exact input headers. -/
theorem readSectionContentsList_headers {headers file contents rest}
    (success : readSectionContentsList headers file = .done contents rest) :
    contents.map SectionContents.header = headers := by
  induction headers generalizing contents rest with
  | nil =>
      simp only [readSectionContentsList] at success
      injection success with contentsEq
      rw [← contentsEq]
      rfl
  | cons header headers ih =>
      simp only [readSectionContentsList] at success
      split at success <;> try contradiction
      next content ignored parsedContent =>
        split at success <;> try contradiction
        next tail ignoredTail parsedTail =>
          injection success with contentsEq
          rw [← contentsEq]
          change content.header :: tail.map SectionContents.header = header :: headers
          have headerEq : content.header = header := by
            simp only [readSectionContents] at parsedContent
            split at parsedContent <;> try contradiction
            split at parsedContent <;> try contradiction
            split at parsedContent <;> try contradiction
            split at parsedContent <;> try contradiction
            next rawData rawRest relocations relocationRest lineNumbers lineRest =>
              injection parsedContent with valueEq
              rw [← valueEq]
          rw [headerEq, ih parsedTail]

/-- Read either no symbol tail or the complete symbol and string tables to EOF. -/
def readSymbolTail (header : Header) (file : Std.Logical.ByteArray) :
    ParseResult (SymbolTail header) :=
  if pointerZero : header.pointerToSymbolTable.toNat = 0 then
    if countZero : header.numberOfSymbols.toNat = 0 then
      .done (.absent pointerZero countZero) Vec.empty
    else
      .invalid (.malformed "zero COFF symbol pointer with nonzero symbol count")
  else
    let minimumEnd := header.symbolTableSpan.endExclusive + 4
    if _ : minimumEnd ≤ file.length then
      match readAuxValidatedSymbolTable header
          (file.drop header.pointerToSymbolTable.toNat) with
      | .done symbols afterSymbols =>
        match readStringTable afterSymbols with
        | .done strings suffix =>
          if suffix.isEmpty then
            if namesValid : symbols.NamesValid strings then
              .done (.present pointerZero symbols strings namesValid) Vec.empty
            else .invalid (.malformed "COFF primary symbol name is invalid")
          else .invalid .trailingInput
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else .needMore (some (minimumEnd - file.length))

/-- A zero pointer and zero count parse as the canonical absent symbol tail. -/
@[simp] theorem readSymbolTail_absent (header : Header)
    (file : Std.Logical.ByteArray)
    (pointerZero : header.pointerToSymbolTable.toNat = 0)
    (countZero : header.numberOfSymbols.toNat = 0) :
    readSymbolTail header file =
      .done (.absent pointerZero countZero) Vec.empty := by
  simp [readSymbolTail, pointerZero, countZero]

/-- An exact addressed symbol/string serialization composes into the canonical
present tail while enforcing the reader's whole-tail EOF condition. -/
theorem readSymbolTail_present_of_region (header : Header)
    (file : Std.Logical.ByteArray)
    (symbols : AuxValidatedSymbolTable header) (strings : StringTable)
    (pointerNonzero : header.pointerToSymbolTable.toNat ≠ 0)
    (namesValid : symbols.NamesValid strings)
    (minimumFits : header.symbolTableSpan.endExclusive + 4 ≤ file.length)
    (regionAt : file.drop header.pointerToSymbolTable.toNat =
      writeAuxValidatedSymbolTable symbols ++ writeStringTable strings) :
    readSymbolTail header file =
      .done (.present pointerNonzero symbols strings namesValid) Vec.empty := by
  simp only [readSymbolTail, pointerNonzero, dite_false, minimumFits, dite_true]
  rw [regionAt, readAuxValidatedSymbolTable_write_append]
  simp only
  rw [readStringTable_writeStringTable]
  simp [Vec.isEmpty, Vec.empty, namesValid]

/-- Parse and validate one complete relocatable-object byte array. -/
def readObject (file : Std.Logical.ByteArray) : ParseResult Object :=
  match readHeader file with
  | .done header afterHeader =>
    if optionalZero : header.sizeOfOptionalHeader.toNat = 0 then
      let required := 40 * header.numberOfSections.toNat
      if required ≤ afterHeader.length then
        match parsedSections : readSectionHeaders
            header.numberOfSections.toNat afterHeader with
        | .done sections _ =>
          if sectionCount : sections.length = header.numberOfSections.toNat then
            let table : SectionTable := { header, sections, sectionCount }
            match parsedContents : readSectionContentsList sections.toList file with
            | .done contentList contentRest =>
              match readSymbolTail header file with
              | .done symbols _ =>
                let contents := Vec.fromList contentList
                have headers :
                    contents.map SectionContents.header = sections := by
                  apply Vec.toList_injective
                  change contentList.map SectionContents.header = sections.toList
                  exact readSectionContentsList_headers (file := file)
                    (contents := contentList) (rest := contentRest)
                    parsedContents
                if valid : DeclaredObjectLayoutValid header sections
                    symbols.stringTable? file.length then
                  .done {
                    bytes := file
                    table
                    contents
                    contentHeaders := headers
                    symbols
                    layoutValid := valid } Vec.empty
                else
                  .invalid
                    (.malformed "COFF object spans overlap or exceed the file")
              | .needMore hint => .needMore hint
              | .invalid error => .invalid error
            | .needMore hint => .needMore hint
            | .invalid error => .invalid error
          else .invalid (.malformed "COFF section-table count mismatch")
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      else .needMore (some (required - afterHeader.length))
    else .invalid (.unsupported "COFF relocatable object optional header")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

end Grass.Artifact.COFF
