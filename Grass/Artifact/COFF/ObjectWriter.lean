import Grass.Artifact.COFF.Object

/-!
# Canonical COFF relocatable-object writer

The writer consumes only raw layout data: uninterpreted section bytes, raw
relocation and line-number records, raw symbol cells, and an optional parsed
string table. It derives all section counts and file pointers from canonical
contiguous placement and rejects values that do not fit their COFF fields.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Raw contents and retained non-placement fields for one output section. -/
structure SectionDescription where
  name : SizedByteArray 8
  physicalAddressOrVirtualSize : BitVec 32
  virtualAddress : BitVec 32
  rawData : Std.Logical.ByteArray
  relocations : Vec Relocation
  lineNumbers : Vec LineNumber
  characteristics : BitVec 32
deriving DecidableEq, Repr

/-- Optional raw symbol cells followed by their parsed string table. -/
inductive SymbolDescription where
  | absent
  | present (cells : Vec SymbolCell) (strings : StringTable)
deriving DecidableEq, Repr

/-- Low-level object description accepted by the canonical writer. -/
structure ObjectDescription where
  machine : BitVec 16
  timeDateStamp : BitVec 32
  characteristics : BitVec 16
  sections : Vec SectionDescription
  symbols : SymbolDescription
deriving DecidableEq, Repr

/-- Serialized byte width of one canonically packed section description. -/
def SectionDescription.byteLength (description : SectionDescription) : Nat :=
  description.rawData.length + 10 * description.relocations.length +
    6 * description.lineNumbers.length

/-- Whether every per-section count and byte extent fits its on-disk field. -/
def SectionDescription.widthsFit (description : SectionDescription) : Bool :=
  description.rawData.length < 2 ^ 32 &&
  description.relocations.length < 2 ^ 16 &&
  description.lineNumbers.length < 2 ^ 16

/-- Canonical pointer value, using zero exactly for an empty extent. -/
private def extentPointer (offset length : Nat) : BitVec 32 :=
  if length = 0 then 0 else BitVec.ofNat 32 offset

/-- Synthesize one section header at its canonical starting file offset. -/
def SectionDescription.headerAt (description : SectionDescription)
    (offset : Nat) : SectionHeader :=
  let relocationOffset := offset + description.rawData.length
  let lineNumberOffset := relocationOffset + 10 * description.relocations.length
  { name := description.name
    physicalAddressOrVirtualSize := description.physicalAddressOrVirtualSize
    virtualAddress := description.virtualAddress
    sizeOfRawData := BitVec.ofNat 32 description.rawData.length
    pointerToRawData := extentPointer offset description.rawData.length
    pointerToRelocations := extentPointer relocationOffset
      description.relocations.length
    pointerToLineNumbers := extentPointer lineNumberOffset
      description.lineNumbers.length
    numberOfRelocations := BitVec.ofNat 16 description.relocations.length
    numberOfLineNumbers := BitVec.ofNat 16 description.lineNumbers.length
    characteristics := description.characteristics }

/-- A representable raw-data length is recovered exactly from its header field. -/
@[simp] theorem SectionDescription.headerAt_sizeOfRawData
    (description : SectionDescription) (offset : Nat)
    (fits : description.rawData.length < 2 ^ 32) :
    (description.headerAt offset).sizeOfRawData.toNat =
      description.rawData.length := by
  simp [SectionDescription.headerAt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fits]

/-- A representable relocation count is recovered exactly from its header field. -/
@[simp] theorem SectionDescription.headerAt_numberOfRelocations
    (description : SectionDescription) (offset : Nat)
    (fits : description.relocations.length < 2 ^ 16) :
    (description.headerAt offset).numberOfRelocations.toNat =
      description.relocations.length := by
  simp [SectionDescription.headerAt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fits]

/-- A representable line count is recovered exactly from its header field. -/
@[simp] theorem SectionDescription.headerAt_numberOfLineNumbers
    (description : SectionDescription) (offset : Nat)
    (fits : description.lineNumbers.length < 2 ^ 16) :
    (description.headerAt offset).numberOfLineNumbers.toNat =
      description.lineNumbers.length := by
  simp [SectionDescription.headerAt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fits]

/-- Nonempty raw data retains its canonical starting offset exactly. -/
@[simp] theorem SectionDescription.headerAt_pointerToRawData_of_pos
    (description : SectionDescription) (offset : Nat)
    (nonempty : 0 < description.rawData.length) (fits : offset < 2 ^ 32) :
    (description.headerAt offset).pointerToRawData.toNat = offset := by
  simp [SectionDescription.headerAt, extentPointer, Nat.ne_of_gt nonempty,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- Empty raw data receives the canonical zero pointer. -/
@[simp] theorem SectionDescription.headerAt_pointerToRawData_of_empty
    (description : SectionDescription) (offset : Nat)
    (empty : description.rawData.length = 0) :
    (description.headerAt offset).pointerToRawData.toNat = 0 := by
  simp [SectionDescription.headerAt, extentPointer, empty]

/-- Nonempty relocations retain their exact offset after the raw data. -/
@[simp] theorem SectionDescription.headerAt_pointerToRelocations_of_pos
    (description : SectionDescription) (offset : Nat)
    (nonempty : 0 < description.relocations.length)
    (fits : offset + description.rawData.length < 2 ^ 32) :
    (description.headerAt offset).pointerToRelocations.toNat =
      offset + description.rawData.length := by
  simp [SectionDescription.headerAt, extentPointer, Nat.ne_of_gt nonempty,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- An empty relocation block receives the canonical zero pointer. -/
@[simp] theorem SectionDescription.headerAt_pointerToRelocations_of_empty
    (description : SectionDescription) (offset : Nat)
    (empty : description.relocations.length = 0) :
    (description.headerAt offset).pointerToRelocations.toNat = 0 := by
  simp [SectionDescription.headerAt, extentPointer, empty]

/-- Nonempty line records retain their exact offset after raw data and relocations. -/
@[simp] theorem SectionDescription.headerAt_pointerToLineNumbers_of_pos
    (description : SectionDescription) (offset : Nat)
    (nonempty : 0 < description.lineNumbers.length)
    (fits : offset + description.rawData.length +
      10 * description.relocations.length < 2 ^ 32) :
    (description.headerAt offset).pointerToLineNumbers.toNat =
      offset + description.rawData.length +
        10 * description.relocations.length := by
  simp [SectionDescription.headerAt, extentPointer, Nat.ne_of_gt nonempty,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- An empty line-number block receives the canonical zero pointer. -/
@[simp] theorem SectionDescription.headerAt_pointerToLineNumbers_of_empty
    (description : SectionDescription) (offset : Nat)
    (empty : description.lineNumbers.length = 0) :
    (description.headerAt offset).pointerToLineNumbers.toNat = 0 := by
  simp [SectionDescription.headerAt, extentPointer, empty]

/-- Representable canonical section headers have coherent zero/nonzero pointers. -/
theorem SectionDescription.headerAt_pointersCoherent
    (description : SectionDescription) (offset : Nat)
    (offsetPositive : 0 < offset)
    (rawFits : description.rawData.length < 2 ^ 32)
    (relocationCountFits : description.relocations.length < 2 ^ 16)
    (lineCountFits : description.lineNumbers.length < 2 ^ 16)
    (endFits : offset + description.byteLength < 2 ^ 32) :
    (description.headerAt offset).PointersCoherent := by
  have offsetFits : offset < 2 ^ 32 := by
    unfold SectionDescription.byteLength at endFits
    omega
  have relocationOffsetFits :
      offset + description.rawData.length < 2 ^ 32 := by
    unfold SectionDescription.byteLength at endFits
    omega
  have lineOffsetFits :
      offset + description.rawData.length +
        10 * description.relocations.length < 2 ^ 32 := by
    unfold SectionDescription.byteLength at endFits
    omega
  have rawCoherent :
      (description.headerAt offset).rawDataSpan.PointerCoherent := by
    change (description.headerAt offset).pointerToRawData.toNat = 0 ↔
      (description.headerAt offset).sizeOfRawData.toNat = 0
    rw [description.headerAt_sizeOfRawData offset rawFits]
    by_cases empty : description.rawData.length = 0
    · rw [description.headerAt_pointerToRawData_of_empty offset empty]
      simp [empty]
    · have positive := Nat.pos_of_ne_zero empty
      rw [description.headerAt_pointerToRawData_of_pos offset positive offsetFits]
      constructor <;> intro impossible <;> omega
  have relocationsCoherent :
      (description.headerAt offset).relocationSpan.PointerCoherent := by
    change (description.headerAt offset).pointerToRelocations.toNat = 0 ↔
      10 * (description.headerAt offset).numberOfRelocations.toNat = 0
    rw [description.headerAt_numberOfRelocations offset relocationCountFits]
    by_cases empty : description.relocations.length = 0
    · rw [description.headerAt_pointerToRelocations_of_empty offset empty]
      simp [empty]
    · have positive := Nat.pos_of_ne_zero empty
      rw [description.headerAt_pointerToRelocations_of_pos offset positive
        relocationOffsetFits]
      constructor <;> intro impossible <;> omega
  have linesCoherent :
      (description.headerAt offset).lineNumberSpan.PointerCoherent := by
    change (description.headerAt offset).pointerToLineNumbers.toNat = 0 ↔
      6 * (description.headerAt offset).numberOfLineNumbers.toNat = 0
    rw [description.headerAt_numberOfLineNumbers offset lineCountFits]
    by_cases empty : description.lineNumbers.length = 0
    · rw [description.headerAt_pointerToLineNumbers_of_empty offset empty]
      simp [empty]
    · have positive := Nat.pos_of_ne_zero empty
      rw [description.headerAt_pointerToLineNumbers_of_pos offset positive
        lineOffsetFits]
      constructor <;> intro impossible <;> omega
  exact ⟨rawCoherent, relocationsCoherent, linesCoherent⟩

/-- Repackage a raw section description as the dependent value expected by the
section-content reader. The three hypotheses are precisely the on-disk field
width obligations used by `SectionDescription.headerAt`. -/
def SectionDescription.contentsAt (description : SectionDescription)
    (offset : Nat)
    (rawFits : description.rawData.length < 2 ^ 32)
    (relocationCountFits : description.relocations.length < 2 ^ 16)
    (lineCountFits : description.lineNumbers.length < 2 ^ 16) :
    SectionContents where
  header := description.headerAt offset
  rawData := ⟨description.rawData, by
    symm
    exact description.headerAt_sizeOfRawData offset rawFits⟩
  relocations :=
    { relocations := description.relocations
      relocationCount := by
        symm
        exact description.headerAt_numberOfRelocations offset
          relocationCountFits }
  lineNumbers :=
    { lines := description.lineNumbers
      lineCount := by
        symm
        exact description.headerAt_numberOfLineNumbers offset lineCountFits }

/-- The canonical content value retains the synthesized section header. -/
@[simp] theorem SectionDescription.contentsAt_header
    (description : SectionDescription) (offset : Nat) (rawFits)
    (relocationCountFits) (lineCountFits) :
    (description.contentsAt offset rawFits relocationCountFits
      lineCountFits).header = description.headerAt offset := rfl

/-- The canonical content value retains the raw section bytes exactly. -/
@[simp] theorem SectionDescription.contentsAt_rawData
    (description : SectionDescription) (offset : Nat) (rawFits)
    (relocationCountFits) (lineCountFits) :
    (description.contentsAt offset rawFits relocationCountFits
      lineCountFits).rawData.1 = description.rawData := rfl

/-- The canonical content value retains the relocation records exactly. -/
@[simp] theorem SectionDescription.contentsAt_relocations
    (description : SectionDescription) (offset : Nat) (rawFits)
    (relocationCountFits) (lineCountFits) :
    (description.contentsAt offset rawFits relocationCountFits
      lineCountFits).relocations.relocations = description.relocations := rfl

/-- The canonical content value retains the line-number records exactly. -/
@[simp] theorem SectionDescription.contentsAt_lineNumbers
    (description : SectionDescription) (offset : Nat) (rawFits)
    (relocationCountFits) (lineCountFits) :
    (description.contentsAt offset rawFits relocationCountFits
      lineCountFits).lineNumbers.lines = description.lineNumbers := rfl

/-- Build canonically placed headers and the first offset following all sections. -/
private def layoutSectionList :
    Nat → List SectionDescription → List SectionHeader × Nat
  | offset, [] => ([], offset)
  | offset, description :: descriptions =>
    let header := description.headerAt offset
    let tail := layoutSectionList (offset + description.byteLength) descriptions
    (header :: tail.1, tail.2)

/-- Canonically placed section headers and the first byte of the symbol tail. -/
def ObjectDescription.sectionLayout (description : ObjectDescription) :
    Vec SectionHeader × Nat :=
  let firstSection := 20 + 40 * description.sections.length
  let layout := layoutSectionList firstSection description.sections.toList
  (Vec.fromList layout.1, layout.2)

/-- Number of raw symbol cells in an optional tail. -/
def SymbolDescription.cellCount : SymbolDescription → Nat
  | .absent => 0
  | .present cells _ => cells.length

/-- Synthesize the COFF file header from canonical layout results. -/
def ObjectDescription.header (description : ObjectDescription) : Header :=
  let layout := description.sectionLayout
  { machine := description.machine
    numberOfSections := BitVec.ofNat 16 description.sections.length
    timeDateStamp := description.timeDateStamp
    pointerToSymbolTable := match description.symbols with
      | .absent => 0
      | .present _ _ => BitVec.ofNat 32 layout.2
    numberOfSymbols := BitVec.ofNat 32 description.symbols.cellCount
    sizeOfOptionalHeader := 0
    characteristics := description.characteristics }

/-- A representable synthesized header retains the exact section count. -/
@[simp] theorem ObjectDescription.header_numberOfSections
    (description : ObjectDescription)
    (fits : description.sections.length < 2 ^ 16) :
    description.header.numberOfSections.toNat = description.sections.length := by
  simp [ObjectDescription.header, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- A representable synthesized header retains the exact symbol-cell count. -/
@[simp] theorem ObjectDescription.header_numberOfSymbols
    (description : ObjectDescription)
    (fits : description.symbols.cellCount < 2 ^ 32) :
    description.header.numberOfSymbols.toNat = description.symbols.cellCount := by
  simp [ObjectDescription.header, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- An absent symbol tail synthesizes a zero symbol-table pointer. -/
@[simp] theorem ObjectDescription.header_pointerToSymbolTable_absent
    (description : ObjectDescription)
    (absent : description.symbols = .absent) :
    description.header.pointerToSymbolTable.toNat = 0 := by
  simp [ObjectDescription.header, absent]

/-- A present symbol tail starts exactly after all canonically packed sections. -/
@[simp] theorem ObjectDescription.header_pointerToSymbolTable_present
    (description : ObjectDescription) (cells : Vec SymbolCell)
    (strings : StringTable)
    (present : description.symbols = .present cells strings)
    (fits : description.sectionLayout.2 < 2 ^ 32) :
    description.header.pointerToSymbolTable.toNat =
      description.sectionLayout.2 := by
  simp [ObjectDescription.header, present, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fits]

/-- Relocatable-object synthesis always emits a zero optional-header size. -/
@[simp] theorem ObjectDescription.header_sizeOfOptionalHeader
    (description : ObjectDescription) :
    description.header.sizeOfOptionalHeader.toNat = 0 := by
  simp [ObjectDescription.header]

/-- Serialize one section's raw bytes, relocations, and line numbers in order. -/
def writeSectionDescription (description : SectionDescription) :
    Std.Logical.ByteArray :=
  description.rawData ++ writeRelocations description.relocations ++
    writeLineNumbers description.lineNumbers

/-- `length_writeSectionDescription` agrees with the closed-form section width. -/
@[simp] theorem length_writeSectionDescription (description : SectionDescription) :
    (writeSectionDescription description).length = description.byteLength := by
  simp [writeSectionDescription, SectionDescription.byteLength, Nat.add_assoc]

/-- A canonically packed section whose three regions are nonempty is recovered
exactly from its synthesized header, even inside an arbitrary file prefix and
suffix. Empty-region pointer cases are separate because COFF represents them
with the distinguished zero pointer. -/
theorem readSectionContents_writeSectionDescription_append_of_pos
    (description : SectionDescription) (offset : Nat)
    (filePrefix suffix : Std.Logical.ByteArray)
    (prefixLength : filePrefix.length = offset)
    (rawPositive : 0 < description.rawData.length)
    (relocationPositive : 0 < description.relocations.length)
    (linePositive : 0 < description.lineNumbers.length)
    (rawFits : description.rawData.length < 2 ^ 32)
    (relocationCountFits : description.relocations.length < 2 ^ 16)
    (lineCountFits : description.lineNumbers.length < 2 ^ 16)
    (endFits : offset + description.byteLength < 2 ^ 32) :
    readSectionContents (description.headerAt offset)
        (filePrefix ++ writeSectionDescription description ++ suffix) =
      .done (description.contentsAt offset rawFits relocationCountFits
        lineCountFits) Vec.empty := by
  let contents := description.contentsAt offset rawFits relocationCountFits
    lineCountFits
  have offsetFits : offset < 2 ^ 32 := by
    unfold SectionDescription.byteLength at endFits
    omega
  have relocationOffsetFits :
      offset + description.rawData.length < 2 ^ 32 := by
    unfold SectionDescription.byteLength at endFits
    omega
  have lineOffsetFits :
      offset + description.rawData.length +
        10 * description.relocations.length < 2 ^ 32 := by
    unfold SectionDescription.byteLength at endFits
    omega
  apply readSectionContents_of_regions contents
    (filePrefix ++ writeSectionDescription description ++ suffix)
    (writeRelocations description.relocations ++
      writeLineNumbers description.lineNumbers ++ suffix)
    (writeLineNumbers description.lineNumbers ++ suffix) suffix
  · simp [contents, SectionHeader.requiredContentEnd,
      SectionHeader.rawDataSpan, SectionHeader.relocationSpan,
      SectionHeader.lineNumberSpan, ByteSpan.endExclusive,
      description.headerAt_pointerToRawData_of_pos offset rawPositive
        offsetFits,
      description.headerAt_pointerToRelocations_of_pos offset
        relocationPositive relocationOffsetFits,
      description.headerAt_pointerToLineNumbers_of_pos offset linePositive
        lineOffsetFits,
      description.headerAt_sizeOfRawData offset rawFits,
      description.headerAt_numberOfRelocations offset relocationCountFits,
      description.headerAt_numberOfLineNumbers offset lineCountFits,
      writeSectionDescription, prefixLength]
    omega
  · simp only [contents, SectionDescription.contentsAt_header,
      SectionHeader.rawDataSpan, writeSectionDescription, Vec.append_assoc]
    rw [description.headerAt_pointerToRawData_of_pos offset rawPositive
      offsetFits]
    rw [Vec.drop_append_of_length_eq prefixLength]
    rfl
  · have prefixRawLength :
        (filePrefix ++ description.rawData).length =
          offset + description.rawData.length := by simp [prefixLength]
    simp only [contents, SectionDescription.contentsAt_header,
      SectionHeader.relocationSpan, writeSectionDescription, Vec.append_assoc]
    rw [description.headerAt_pointerToRelocations_of_pos offset
      relocationPositive relocationOffsetFits]
    rw [← Vec.append_assoc filePrefix description.rawData]
    rw [Vec.drop_append_of_length_eq prefixRawLength]
    rfl
  · have prefixRelocationLength :
        (filePrefix ++ description.rawData ++
          writeRelocations description.relocations).length =
          offset + description.rawData.length +
            10 * description.relocations.length := by
      simp [prefixLength]
    simp only [contents, SectionDescription.contentsAt_header,
      SectionHeader.lineNumberSpan, writeSectionDescription, Vec.append_assoc]
    rw [description.headerAt_pointerToLineNumbers_of_pos offset linePositive
      lineOffsetFits]
    rw [← Vec.append_assoc filePrefix description.rawData]
    rw [← Vec.append_assoc (filePrefix ++ description.rawData)
      (writeRelocations description.relocations)]
    rw [Vec.drop_append_of_length_eq prefixRelocationLength]
    rfl

/-- Serialize all section descriptions in source order. -/
private def writeSectionDescriptionList :
    List SectionDescription → Std.Logical.ByteArray
  | [] => Vec.empty
  | description :: descriptions =>
    writeSectionDescription description ++
      writeSectionDescriptionList descriptions

/-- Total serialized width of a list of section descriptions. -/
private def sectionDescriptionListLength : List SectionDescription → Nat
  | [] => 0
  | description :: descriptions =>
    description.byteLength + sectionDescriptionListLength descriptions

/-- Sum of all canonical section-content widths in source order. -/
def ObjectDescription.sectionsByteLength
    (description : ObjectDescription) : Nat :=
  sectionDescriptionListLength description.sections.toList

/-- The recursive section writer realizes `sectionDescriptionListLength`. -/
private theorem length_writeSectionDescriptionList
    (descriptions : List SectionDescription) :
    (writeSectionDescriptionList descriptions).length =
      sectionDescriptionListLength descriptions := by
  induction descriptions with
  | nil => rfl
  | cons description descriptions ih =>
      simp [writeSectionDescriptionList, sectionDescriptionListLength, ih]

/-- Serialize an optional symbol/string-table tail. -/
def writeSymbolDescription : SymbolDescription → Std.Logical.ByteArray
  | .absent => Vec.empty
  | .present cells strings => writeSymbolCells cells ++ writeStringTable strings

/-- Serialized width of an optional symbol/string-table tail. -/
def SymbolDescription.byteLength : SymbolDescription → Nat
  | .absent => 0
  | .present cells strings => 18 * cells.length + strings.declaredSize.toNat

/-- `length_writeSymbolDescription` agrees with the closed-form tail width. -/
@[simp] theorem length_writeSymbolDescription (symbols : SymbolDescription) :
    (writeSymbolDescription symbols).length = symbols.byteLength := by
  cases symbols with
  | absent => rfl
  | present cells strings =>
      simp [writeSymbolDescription, SymbolDescription.byteLength]

/-- `layoutSectionList` emits one synthesized header per source section. -/
private theorem length_layoutSectionList (offset : Nat)
    (descriptions : List SectionDescription) :
    (layoutSectionList offset descriptions).1.length = descriptions.length := by
  induction descriptions generalizing offset with
  | nil => rfl
  | cons description descriptions ih =>
      simp [layoutSectionList, ih]

/-- `layoutSectionList` advances by exactly the summed section byte widths. -/
private theorem end_layoutSectionList (offset : Nat)
    (descriptions : List SectionDescription) :
    (layoutSectionList offset descriptions).2 =
      offset + sectionDescriptionListLength descriptions := by
  induction descriptions generalizing offset with
  | nil => simp [layoutSectionList, sectionDescriptionListLength]
  | cons description descriptions ih =>
      simp [layoutSectionList, sectionDescriptionListLength, ih, Nat.add_assoc]

/-- The synthesized section table retains the source section count. -/
@[simp] theorem ObjectDescription.length_sectionLayout
    (description : ObjectDescription) :
    description.sectionLayout.1.length = description.sections.length := by
  change (layoutSectionList (20 + 40 * description.sections.length)
    description.sections.toList).1.length = description.sections.toList.length
  exact length_layoutSectionList _ _

/-- The symbol-tail offset is the prefix plus all section byte widths. -/
theorem ObjectDescription.end_sectionLayout (description : ObjectDescription) :
    description.sectionLayout.2 =
      20 + 40 * description.sections.length +
        description.sectionsByteLength := by
  simp [ObjectDescription.sectionLayout, ObjectDescription.sectionsByteLength,
    end_layoutSectionList]

/-- Closed-form length of the canonical object serialization. -/
def ObjectDescription.byteLength (description : ObjectDescription) : Nat :=
  20 + 40 * description.sections.length +
    description.sectionsByteLength + description.symbols.byteLength

/-- Unchecked canonical bytes after all derived pointers have been synthesized. -/
def ObjectDescription.bytes (description : ObjectDescription) :
    Std.Logical.ByteArray :=
  let layout := description.sectionLayout
  writeHeader description.header ++ writeSectionHeaders layout.1 ++
    writeSectionDescriptionList description.sections.toList ++
    writeSymbolDescription description.symbols

/-- `length_bytes` proves the canonical writer's closed-form total size. -/
@[simp] theorem ObjectDescription.length_bytes (description : ObjectDescription) :
    description.bytes.length = description.byteLength := by
  simp [ObjectDescription.bytes, ObjectDescription.byteLength,
    ObjectDescription.sectionsByteLength, length_writeSectionDescriptionList,
    Nat.add_assoc]

/-- Whether every derived count, pointer, and total size fits its COFF field. -/
def ObjectDescription.widthsFit (description : ObjectDescription) : Bool :=
  let layout := description.sectionLayout
  let totalLength := description.byteLength
  description.sections.length < 2 ^ 16 &&
  description.sections.toList.all SectionDescription.widthsFit &&
  description.symbols.cellCount < 2 ^ 32 &&
  layout.2 < 2 ^ 32 && totalLength < 2 ^ 32

/-- Validate widths plus auxiliary and primary-name structure before writing. -/
def ObjectDescription.Writable (description : ObjectDescription) : Bool :=
  description.widthsFit &&
  match description.symbols with
  | .absent => true
  | .present cells strings =>
    validAuxLayoutScan cells.length cells.toList &&
      validPrimaryNamesScan cells.length cells.toList strings

/-- Emit canonical object bytes or reject an unrepresentable raw description. -/
def writeObjectDescription (description : ObjectDescription) :
    Except ParseError Std.Logical.ByteArray :=
  if description.widthsFit then
    match description.symbols with
    | .absent => .ok description.bytes
    | .present cells strings =>
      if validAuxLayoutScan cells.length cells.toList then
        if validPrimaryNamesScan cells.length cells.toList strings then
          .ok description.bytes
        else .error (.malformed "COFF primary symbol name is invalid")
      else .error (.malformed "COFF auxiliary symbol layout is inconsistent")
  else .error (.arithmeticOverflow "COFF object layout exceeds field width")

/-- Every successful write returns exactly `ObjectDescription.bytes`. -/
theorem writeObjectDescription_ok {description : ObjectDescription}
    {bytes : Std.Logical.ByteArray}
    (success : writeObjectDescription description = .ok bytes) :
    bytes = description.bytes := by
  unfold writeObjectDescription at success
  split at success <;> try contradiction
  next widths =>
    split at success
    next => injection success with bytesEq; exact bytesEq.symm
    next cells strings =>
      split at success <;> try contradiction
      split at success <;> try contradiction
      injection success with bytesEq
      exact bytesEq.symm

/-- A successful canonical result is equivalent to the complete `Writable` check. -/
theorem writeObjectDescription_ok_iff (description : ObjectDescription) :
    writeObjectDescription description = .ok description.bytes ↔
      description.Writable = true := by
  cases widths : description.widthsFit with
  | false => simp [writeObjectDescription, ObjectDescription.Writable, widths]
  | true =>
    cases symbols : description.symbols with
    | absent =>
      simp [writeObjectDescription, ObjectDescription.Writable, widths, symbols]
    | present cells strings =>
      cases auxiliary : validAuxLayoutScan cells.length cells.toList with
      | false =>
        simp [writeObjectDescription, ObjectDescription.Writable, widths,
          symbols, auxiliary]
      | true =>
        cases names : validPrimaryNamesScan cells.length cells.toList strings with
        | false =>
          simp [writeObjectDescription, ObjectDescription.Writable, widths,
            symbols, auxiliary, names]
        | true =>
          simp [writeObjectDescription, ObjectDescription.Writable, widths,
            symbols, auxiliary, names]

/-- Successful canonical output has the declared length and fits 32-bit offsets. -/
theorem writeObjectDescription_ok_length {description : ObjectDescription}
    {bytes : Std.Logical.ByteArray}
    (success : writeObjectDescription description = .ok bytes) :
    bytes.length = description.byteLength ∧
      description.byteLength < 2 ^ 32 := by
  have bytesEq := writeObjectDescription_ok success
  have writable : description.Writable = true := by
    apply (writeObjectDescription_ok_iff description).mp
    rw [← bytesEq]
    exact success
  have widths : description.widthsFit = true := by
    cases widthsValue : description.widthsFit with
    | false => simp [ObjectDescription.Writable, widthsValue] at writable
    | true => rfl
  have total : description.byteLength < 2 ^ 32 := by
    unfold ObjectDescription.widthsFit at widths
    simp at widths
    omega
  constructor
  · rw [bytesEq]
    exact ObjectDescription.length_bytes description
  · exact total

end Grass.Artifact.COFF
