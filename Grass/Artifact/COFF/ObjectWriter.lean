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

/-- The executable per-section width check is exactly the three field bounds
needed to construct header-indexed contents. -/
theorem SectionDescription.widthsFit_iff (description : SectionDescription) :
    description.widthsFit = true ↔
      description.rawData.length < 2 ^ 32 ∧
      description.relocations.length < 2 ^ 16 ∧
      description.lineNumbers.length < 2 ^ 16 := by
  simp [SectionDescription.widthsFit, and_assoc]

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

/-- Every synthesized section span is either the canonical empty span at zero
or lies wholly inside that section's contiguous canonical byte interval. -/
theorem SectionDescription.headerAt_declaredSpan_bounds
    (description : SectionDescription) (offset : Nat)
    (rawFits : description.rawData.length < 2 ^ 32)
    (relocationCountFits : description.relocations.length < 2 ^ 16)
    (lineCountFits : description.lineNumbers.length < 2 ^ 16)
    (endFits : offset + description.byteLength < 2 ^ 32)
    {span : ByteSpan}
    (member : span ∈ (description.headerAt offset).declaredSpans) :
    (span.offset = 0 ∧ span.length = 0) ∨
      (offset ≤ span.offset ∧
        span.endExclusive ≤ offset + description.byteLength) := by
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
  simp [SectionHeader.declaredSpans] at member
  rcases member with rfl | rfl | rfl
  · by_cases empty : description.rawData.length = 0
    · left
      simp [SectionHeader.rawDataSpan,
        description.headerAt_pointerToRawData_of_empty offset empty,
        description.headerAt_sizeOfRawData offset rawFits, empty]
    · right
      simp [SectionHeader.rawDataSpan, ByteSpan.endExclusive,
        description.headerAt_pointerToRawData_of_pos offset
          (Nat.pos_of_ne_zero empty) offsetFits,
        description.headerAt_sizeOfRawData offset rawFits,
        SectionDescription.byteLength]
      omega
  · by_cases empty : description.relocations.length = 0
    · left
      simp [SectionHeader.relocationSpan,
        description.headerAt_pointerToRelocations_of_empty offset empty,
        description.headerAt_numberOfRelocations offset relocationCountFits,
        empty]
    · right
      simp [SectionHeader.relocationSpan, ByteSpan.endExclusive,
        description.headerAt_pointerToRelocations_of_pos offset
          (Nat.pos_of_ne_zero empty) relocationOffsetFits,
        description.headerAt_numberOfRelocations offset relocationCountFits,
        SectionDescription.byteLength]
      omega
  · by_cases empty : description.lineNumbers.length = 0
    · left
      simp [SectionHeader.lineNumberSpan,
        description.headerAt_pointerToLineNumbers_of_empty offset empty,
        description.headerAt_numberOfLineNumbers offset lineCountFits, empty]
    · right
      simp [SectionHeader.lineNumberSpan, ByteSpan.endExclusive,
        description.headerAt_pointerToLineNumbers_of_pos offset
          (Nat.pos_of_ne_zero empty) lineOffsetFits,
        description.headerAt_numberOfLineNumbers offset lineCountFits,
        SectionDescription.byteLength]
      omega

/-- The raw-data, relocation, and line-number spans synthesized for one
canonical section are pairwise disjoint, including all zero-width cases. -/
theorem SectionDescription.headerAt_declaredSpans_pairwise
    (description : SectionDescription) (offset : Nat)
    (rawFits : description.rawData.length < 2 ^ 32)
    (relocationCountFits : description.relocations.length < 2 ^ 16)
    (lineCountFits : description.lineNumbers.length < 2 ^ 16)
    (endFits : offset + description.byteLength < 2 ^ 32) :
    ((description.headerAt offset).declaredSpans).Pairwise ByteSpan.Disjoint := by
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
  by_cases rawEmpty : description.rawData.length = 0
  all_goals by_cases relocationEmpty : description.relocations.length = 0
  all_goals by_cases lineEmpty : description.lineNumbers.length = 0
  all_goals simp [SectionHeader.declaredSpans, ByteSpan.Disjoint,
    ByteSpan.endExclusive, SectionHeader.rawDataSpan,
    SectionHeader.relocationSpan, SectionHeader.lineNumberSpan,
    SectionDescription.headerAt, extentPointer, rawEmpty, relocationEmpty,
    lineEmpty, BitVec.toNat_ofNat, Nat.mod_eq_of_lt rawFits,
    Nat.mod_eq_of_lt relocationCountFits,
    Nat.mod_eq_of_lt lineCountFits, Nat.mod_eq_of_lt offsetFits,
    Nat.mod_eq_of_lt relocationOffsetFits, Nat.mod_eq_of_lt lineOffsetFits]
  all_goals omega

/-- Every span of one canonical section fits any container that reaches the
end of that section's contiguous byte interval. -/
theorem SectionDescription.headerAt_declaredSpans_fit
    (description : SectionDescription) (offset containerLength : Nat)
    (rawFits : description.rawData.length < 2 ^ 32)
    (relocationCountFits : description.relocations.length < 2 ^ 16)
    (lineCountFits : description.lineNumbers.length < 2 ^ 16)
    (addressFits : offset + description.byteLength < 2 ^ 32)
    (sectionFits : offset + description.byteLength ≤ containerLength) :
    ∀ span ∈ (description.headerAt offset).declaredSpans,
      span.Fits containerLength := by
  intro span member
  rcases description.headerAt_declaredSpan_bounds offset rawFits
      relocationCountFits lineCountFits addressFits member with empty | bounded
  · unfold ByteSpan.Fits ByteSpan.endExclusive
    omega
  · exact Nat.le_trans bounded.2 sectionFits

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
def layoutSectionList :
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

/-- Canonical section bytes parse back to their exact dependent contents for
every combination of present and absent raw-data, relocation, and line-number
regions. An absent region is read at COFF's distinguished zero pointer and its
zero-width reader leaves the complete file untouched. -/
theorem readSectionContents_writeSectionDescription_append
    (description : SectionDescription) (offset : Nat)
    (filePrefix suffix : Std.Logical.ByteArray)
    (prefixLength : filePrefix.length = offset)
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
  let file := filePrefix ++ writeSectionDescription description ++ suffix
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
  have rawPointer :
      (description.headerAt offset).pointerToRawData.toNat =
        if description.rawData.length = 0 then 0 else offset := by
    by_cases empty : description.rawData.length = 0
    · simp [empty,
        description.headerAt_pointerToRawData_of_empty offset empty]
    · simp [empty, description.headerAt_pointerToRawData_of_pos offset
        (Nat.pos_of_ne_zero empty) offsetFits]
  have relocationPointer :
      (description.headerAt offset).pointerToRelocations.toNat =
        if description.relocations.length = 0 then 0
        else offset + description.rawData.length := by
    by_cases empty : description.relocations.length = 0
    · simp [empty,
        description.headerAt_pointerToRelocations_of_empty offset empty]
    · simp [empty, description.headerAt_pointerToRelocations_of_pos offset
        (Nat.pos_of_ne_zero empty) relocationOffsetFits]
  have linePointer :
      (description.headerAt offset).pointerToLineNumbers.toNat =
        if description.lineNumbers.length = 0 then 0
        else offset + description.rawData.length +
          10 * description.relocations.length := by
    by_cases empty : description.lineNumbers.length = 0
    · simp [empty,
        description.headerAt_pointerToLineNumbers_of_empty offset empty]
    · simp [empty, description.headerAt_pointerToLineNumbers_of_pos offset
        (Nat.pos_of_ne_zero empty) lineOffsetFits]
  have rawRegion : ∃ rest,
      file.drop contents.header.rawDataSpan.offset =
        writeSectionRawData contents.rawData ++ rest := by
    by_cases empty : description.rawData.length = 0
    · have rawEmpty : description.rawData = Vec.empty :=
        (Vec.eq_empty_iff_length_eq_zero description.rawData).2 empty
      refine ⟨file, ?_⟩
      simp [file, contents, SectionHeader.rawDataSpan,
        description.headerAt_pointerToRawData_of_empty offset empty,
        writeSectionRawData, writeExact, rawEmpty]
    · have positive := Nat.pos_of_ne_zero empty
      refine ⟨writeRelocations description.relocations ++
        writeLineNumbers description.lineNumbers ++ suffix, ?_⟩
      simp only [file, contents, SectionDescription.contentsAt_header,
        SectionHeader.rawDataSpan, writeSectionDescription, Vec.append_assoc]
      rw [description.headerAt_pointerToRawData_of_pos offset positive
        offsetFits]
      rw [Vec.drop_append_of_length_eq prefixLength]
      rfl
  have relocationRegion : ∃ rest,
      file.drop contents.header.relocationSpan.offset =
        writeRelocationBlock contents.relocations ++ rest := by
    by_cases empty : description.relocations.length = 0
    · have writtenEmpty : writeRelocations description.relocations = Vec.empty :=
        (Vec.eq_empty_iff_length_eq_zero _).2 (by simp [empty])
      refine ⟨file, ?_⟩
      have pointerZero : contents.header.relocationSpan.offset = 0 := by
        simp [contents, SectionHeader.relocationSpan,
          description.headerAt_pointerToRelocations_of_empty offset empty]
      have blockEmpty : writeRelocationBlock contents.relocations = Vec.empty := by
        change writeRelocations description.relocations = Vec.empty
        exact writtenEmpty
      rw [pointerZero, Vec.drop_zero, blockEmpty, Vec.empty_append]
    · have positive := Nat.pos_of_ne_zero empty
      have prefixRawLength :
          (filePrefix ++ description.rawData).length =
            offset + description.rawData.length := by simp [prefixLength]
      refine ⟨writeLineNumbers description.lineNumbers ++ suffix, ?_⟩
      simp only [file, contents, SectionDescription.contentsAt_header,
        SectionHeader.relocationSpan, writeSectionDescription,
        Vec.append_assoc]
      rw [description.headerAt_pointerToRelocations_of_pos offset positive
        relocationOffsetFits]
      rw [← Vec.append_assoc filePrefix description.rawData]
      rw [Vec.drop_append_of_length_eq prefixRawLength]
      rfl
  have lineRegion : ∃ rest,
      file.drop contents.header.lineNumberSpan.offset =
        writeLineNumberBlock contents.lineNumbers ++ rest := by
    by_cases empty : description.lineNumbers.length = 0
    · have writtenEmpty : writeLineNumbers description.lineNumbers = Vec.empty :=
        (Vec.eq_empty_iff_length_eq_zero _).2 (by simp [empty])
      refine ⟨file, ?_⟩
      have pointerZero : contents.header.lineNumberSpan.offset = 0 := by
        simp [contents, SectionHeader.lineNumberSpan,
          description.headerAt_pointerToLineNumbers_of_empty offset empty]
      have blockEmpty : writeLineNumberBlock contents.lineNumbers = Vec.empty := by
        change writeLineNumbers description.lineNumbers = Vec.empty
        exact writtenEmpty
      rw [pointerZero, Vec.drop_zero, blockEmpty, Vec.empty_append]
    · have positive := Nat.pos_of_ne_zero empty
      have prefixRelocationLength :
          (filePrefix ++ description.rawData ++
            writeRelocations description.relocations).length =
            offset + description.rawData.length +
              10 * description.relocations.length := by
        simp [prefixLength]
      refine ⟨suffix, ?_⟩
      simp only [file, contents, SectionDescription.contentsAt_header,
        SectionHeader.lineNumberSpan, writeSectionDescription,
        Vec.append_assoc]
      rw [description.headerAt_pointerToLineNumbers_of_pos offset positive
        lineOffsetFits]
      rw [← Vec.append_assoc filePrefix description.rawData]
      rw [← Vec.append_assoc (filePrefix ++ description.rawData)
        (writeRelocations description.relocations)]
      rw [Vec.drop_append_of_length_eq prefixRelocationLength]
      rfl
  rcases rawRegion with ⟨rawSuffix, rawAt⟩
  rcases relocationRegion with ⟨relocationSuffix, relocationsAt⟩
  rcases lineRegion with ⟨lineSuffix, linesAt⟩
  apply readSectionContents_of_regions contents file rawSuffix relocationSuffix
    lineSuffix
  · simp only [file, contents, SectionDescription.contentsAt_header,
      SectionHeader.requiredContentEnd, SectionHeader.rawDataSpan,
      SectionHeader.relocationSpan, SectionHeader.lineNumberSpan,
      ByteSpan.endExclusive, Vec.length_append, length_writeSectionDescription]
    rw [description.headerAt_sizeOfRawData offset rawFits]
    rw [description.headerAt_numberOfRelocations offset relocationCountFits]
    rw [description.headerAt_numberOfLineNumbers offset lineCountFits]
    rw [rawPointer, relocationPointer, linePointer]
    by_cases rawEmpty : description.rawData.length = 0
    all_goals by_cases relocationEmpty : description.relocations.length = 0
    all_goals by_cases lineEmpty : description.lineNumbers.length = 0
    all_goals simp_all
    all_goals unfold SectionDescription.byteLength at endFits ⊢
    all_goals omega
  · exact rawAt
  · exact relocationsAt
  · exact linesAt

/-- Serialize all section descriptions in source order. -/
def writeSectionDescriptionList :
    List SectionDescription → Std.Logical.ByteArray
  | [] => Vec.empty
  | description :: descriptions =>
    writeSectionDescription description ++
      writeSectionDescriptionList descriptions

/-- Total serialized width of a list of section descriptions. -/
def sectionDescriptionListLength : List SectionDescription → Nat
  | [] => 0
  | description :: descriptions =>
    description.byteLength + sectionDescriptionListLength descriptions

/-- Spans synthesized by a canonical section list are either empty at zero or
bounded by the complete contiguous interval assigned to that list. -/
theorem layoutSectionList_declaredSpan_bounds (offset : Nat)
    (descriptions : List SectionDescription)
    (widths : ∀ description ∈ descriptions,
      description.widthsFit = true)
    (endFits : offset + sectionDescriptionListLength descriptions < 2 ^ 32)
    {span : ByteSpan}
    (member : span ∈ (layoutSectionList offset descriptions).1.flatMap
      SectionHeader.declaredSpans) :
    (span.offset = 0 ∧ span.length = 0) ∨
      (offset ≤ span.offset ∧ span.endExclusive ≤
        offset + sectionDescriptionListLength descriptions) := by
  induction descriptions generalizing offset with
  | nil => simp [layoutSectionList] at member
  | cons description descriptions ih =>
      have descriptionWidth := description.widthsFit_iff.mp
        (widths description (by simp))
      have tailWidths : ∀ tail ∈ descriptions, tail.widthsFit = true :=
        fun tail tailMember => widths tail (by simp [tailMember])
      have headEndFits : offset + description.byteLength < 2 ^ 32 := by
        unfold sectionDescriptionListLength at endFits
        omega
      have tailEndFits : offset + description.byteLength +
          sectionDescriptionListLength descriptions < 2 ^ 32 := by
        unfold sectionDescriptionListLength at endFits
        omega
      simp only [layoutSectionList, List.flatMap_cons, List.mem_append] at member
      rcases member with headMember | tailMember
      · rcases description.headerAt_declaredSpan_bounds offset
          descriptionWidth.1 descriptionWidth.2.1 descriptionWidth.2.2
          headEndFits headMember with empty | bounded
        · exact Or.inl empty
        · right
          unfold sectionDescriptionListLength
          constructor
          · exact bounded.1
          · omega
      · rcases ih (offset + description.byteLength) tailWidths tailEndFits
          tailMember with empty | bounded
        · exact Or.inl empty
        · right
          unfold sectionDescriptionListLength
          constructor <;> omega

/-- All spans synthesized by a canonical section list are pairwise disjoint,
including empty spans represented at pointer zero. -/
theorem layoutSectionList_declaredSpans_pairwise (offset : Nat)
    (descriptions : List SectionDescription)
    (widths : ∀ description ∈ descriptions,
      description.widthsFit = true)
    (endFits : offset + sectionDescriptionListLength descriptions < 2 ^ 32) :
    ((layoutSectionList offset descriptions).1.flatMap
      SectionHeader.declaredSpans).Pairwise ByteSpan.Disjoint := by
  induction descriptions generalizing offset with
  | nil => simp [layoutSectionList]
  | cons description descriptions ih =>
      have descriptionWidth := description.widthsFit_iff.mp
        (widths description (by simp))
      have tailWidths : ∀ tail ∈ descriptions, tail.widthsFit = true :=
        fun tail tailMember => widths tail (by simp [tailMember])
      have headEndFits : offset + description.byteLength < 2 ^ 32 := by
        unfold sectionDescriptionListLength at endFits
        omega
      have tailEndFits : offset + description.byteLength +
          sectionDescriptionListLength descriptions < 2 ^ 32 := by
        unfold sectionDescriptionListLength at endFits
        omega
      simp only [layoutSectionList, List.flatMap_cons]
      rw [List.pairwise_append]
      refine ⟨description.headerAt_declaredSpans_pairwise offset
          descriptionWidth.1 descriptionWidth.2.1 descriptionWidth.2.2
          headEndFits,
        ih (offset + description.byteLength) tailWidths tailEndFits, ?_⟩
      intro headSpan headMember tailSpan tailMember
      rcases description.headerAt_declaredSpan_bounds offset
          descriptionWidth.1 descriptionWidth.2.1 descriptionWidth.2.2
          headEndFits headMember with headEmpty | headBounded
      · left
        unfold ByteSpan.endExclusive
        omega
      · rcases layoutSectionList_declaredSpan_bounds
          (offset + description.byteLength) descriptions tailWidths tailEndFits
          tailMember with tailEmpty | tailBounded
        · right
          unfold ByteSpan.endExclusive
          omega
        · left
          exact Nat.le_trans headBounded.2 tailBounded.1

/-- Every header synthesized by canonical list layout has coherent zero and
nonzero pointers. -/
theorem layoutSectionList_pointersCoherent (offset : Nat)
    (descriptions : List SectionDescription) (offsetPositive : 0 < offset)
    (widths : ∀ description ∈ descriptions,
      description.widthsFit = true)
    (endFits : offset + sectionDescriptionListLength descriptions < 2 ^ 32) :
    ∀ header ∈ (layoutSectionList offset descriptions).1,
      header.PointersCoherent := by
  induction descriptions generalizing offset with
  | nil => simp [layoutSectionList]
  | cons description descriptions ih =>
      have descriptionWidth := description.widthsFit_iff.mp
        (widths description (by simp))
      have tailWidths : ∀ tail ∈ descriptions, tail.widthsFit = true :=
        fun tail tailMember => widths tail (by simp [tailMember])
      have headEndFits : offset + description.byteLength < 2 ^ 32 := by
        unfold sectionDescriptionListLength at endFits
        omega
      have tailEndFits : offset + description.byteLength +
          sectionDescriptionListLength descriptions < 2 ^ 32 := by
        unfold sectionDescriptionListLength at endFits
        omega
      intro header member
      simp only [layoutSectionList, List.mem_cons] at member
      rcases member with rfl | tailMember
      · exact description.headerAt_pointersCoherent offset offsetPositive
          descriptionWidth.1 descriptionWidth.2.1 descriptionWidth.2.2
          headEndFits
      · exact ih (offset + description.byteLength) (by omega) tailWidths
          tailEndFits header tailMember

/-- Sum of all canonical section-content widths in source order. -/
def ObjectDescription.sectionsByteLength
    (description : ObjectDescription) : Nat :=
  sectionDescriptionListLength description.sections.toList

/-- The recursive section writer realizes `sectionDescriptionListLength`. -/
theorem length_writeSectionDescriptionList
    (descriptions : List SectionDescription) :
    (writeSectionDescriptionList descriptions).length =
      sectionDescriptionListLength descriptions := by
  induction descriptions with
  | nil => rfl
  | cons description descriptions ih =>
      simp [writeSectionDescriptionList, sectionDescriptionListLength, ih]

/-- Construct the dependent section-content values corresponding to a list of
raw descriptions at consecutive canonical offsets. -/
def sectionContentsListAt (offset : Nat)
    (descriptions : List SectionDescription)
    (widths : ∀ description ∈ descriptions,
      description.widthsFit = true) : List SectionContents :=
  match descriptions with
  | [] => []
  | description :: descriptions =>
    have descriptionFits :=
      (description.widthsFit_iff).mp (widths description (by simp))
    description.contentsAt offset descriptionFits.1 descriptionFits.2.1
      descriptionFits.2.2 ::
        sectionContentsListAt (offset + description.byteLength) descriptions
          (fun tail member => widths tail (by simp [member]))

/-- Canonical dependent contents retain exactly the synthesized header list. -/
theorem sectionContentsListAt_headers (offset : Nat)
    (descriptions : List SectionDescription)
    (widths : ∀ description ∈ descriptions,
      description.widthsFit = true) :
    (sectionContentsListAt offset descriptions widths).map
        SectionContents.header =
      (layoutSectionList offset descriptions).1 := by
  induction descriptions generalizing offset with
  | nil => rfl
  | cons description descriptions ih =>
      simp only [sectionContentsListAt, List.map_cons,
        SectionDescription.contentsAt_header, layoutSectionList,
        List.cons.injEq, true_and]
      exact ih (offset + description.byteLength)
        (fun tail member => widths tail (by simp [member]))

/-- Canonically packed section lists parse to the exact dependent content list
at every sequence of representable section widths and offsets. -/
theorem readSectionContentsList_writeSectionDescriptionList_append
    (descriptions : List SectionDescription) (offset : Nat)
    (filePrefix suffix : Std.Logical.ByteArray)
    (prefixLength : filePrefix.length = offset)
    (widths : ∀ description ∈ descriptions,
      description.widthsFit = true)
    (endFits : offset + sectionDescriptionListLength descriptions < 2 ^ 32) :
    readSectionContentsList (layoutSectionList offset descriptions).1
        (filePrefix ++ writeSectionDescriptionList descriptions ++ suffix) =
      .done (sectionContentsListAt offset descriptions widths) Vec.empty := by
  induction descriptions generalizing offset filePrefix with
  | nil => simp [layoutSectionList, writeSectionDescriptionList,
      sectionContentsListAt, readSectionContentsList]
  | cons description descriptions ih =>
      have descriptionFit := widths description (by simp)
      have fieldFits := description.widthsFit_iff.mp descriptionFit
      have tailWidths : ∀ tail ∈ descriptions, tail.widthsFit = true :=
        fun tail member => widths tail (by simp [member])
      have headEndFits : offset + description.byteLength < 2 ^ 32 := by
        unfold sectionDescriptionListLength at endFits
        omega
      have headRead :=
        readSectionContents_writeSectionDescription_append description offset
          filePrefix (writeSectionDescriptionList descriptions ++ suffix)
          prefixLength fieldFits.1 fieldFits.2.1 fieldFits.2.2 headEndFits
      have tailPrefixLength :
          (filePrefix ++ writeSectionDescription description).length =
            offset + description.byteLength := by simp [prefixLength]
      have tailEndFits :
          offset + description.byteLength +
            sectionDescriptionListLength descriptions < 2 ^ 32 := by
        unfold sectionDescriptionListLength at endFits
        omega
      have tailRead := ih (offset + description.byteLength)
        (filePrefix ++ writeSectionDescription description) tailPrefixLength
        tailWidths tailEndFits
      simp only [layoutSectionList, readSectionContentsList,
        writeSectionDescriptionList, sectionContentsListAt]
      simp only [Vec.append_assoc] at headRead tailRead ⊢
      rw [headRead, tailRead]

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
theorem length_layoutSectionList (offset : Nat)
    (descriptions : List SectionDescription) :
    (layoutSectionList offset descriptions).1.length = descriptions.length := by
  induction descriptions generalizing offset with
  | nil => rfl
  | cons description descriptions ih =>
      simp [layoutSectionList, ih]

/-- `layoutSectionList` advances by exactly the summed section byte widths. -/
theorem end_layoutSectionList (offset : Nat)
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

/-- Count-coupled canonical file header and synthesized section headers. -/
def ObjectDescription.sectionTable (description : ObjectDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) : SectionTable where
  header := description.header
  sections := description.sectionLayout.1
  sectionCount := by
    rw [description.length_sectionLayout]
    symm
    exact description.header_numberOfSections sectionCountFits

/-- The canonical section table serializes to the synthesized header followed
by the synthesized section-header vector. -/
theorem ObjectDescription.writeSectionTable_sectionTable
    (description : ObjectDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    writeSectionTable (description.sectionTable sectionCountFits) =
      writeHeader description.header ++
        writeSectionHeaders description.sectionLayout.1 := rfl

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

/-- Reading the canonical table prefix returns the exact synthesized table and
leaves all section contents plus the symbol tail untouched. -/
theorem ObjectDescription.readSectionTable_bytes
    (description : ObjectDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    readSectionTable description.bytes =
      .done (description.sectionTable sectionCountFits)
        (writeSectionDescriptionList description.sections.toList ++
          writeSymbolDescription description.symbols) := by
  have parsed := readSectionTable_writeSectionTable_append
    (description.sectionTable sectionCountFits)
    (writeSectionDescriptionList description.sections.toList ++
      writeSymbolDescription description.symbols)
  simpa only [ObjectDescription.bytes,
    description.writeSectionTable_sectionTable sectionCountFits,
    Vec.append_assoc] using parsed

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

/-- Whole-object width validity supplies every per-section field-width check. -/
theorem ObjectDescription.widthsFit_sections
    (description : ObjectDescription)
    (widths : description.widthsFit = true) :
    ∀ sectionDescription ∈ description.sections.toList,
      sectionDescription.widthsFit = true := by
  unfold ObjectDescription.widthsFit at widths
  simp only [Bool.and_eq_true] at widths
  have sectionWidths :
      description.sections.toList.all SectionDescription.widthsFit = true :=
    widths.1.1.1.2
  simpa only [List.all_eq_true] using sectionWidths

/-- Whole-object width validity supplies the section-count field bound. -/
theorem ObjectDescription.widthsFit_sectionCount
    (description : ObjectDescription)
    (widths : description.widthsFit = true) :
    description.sections.length < 2 ^ 16 := by
  unfold ObjectDescription.widthsFit at widths
  simp only [Bool.and_eq_true] at widths
  exact of_decide_eq_true widths.1.1.1.1

/-- Whole-object width validity supplies the symbol-count field bound. -/
theorem ObjectDescription.widthsFit_symbolCount
    (description : ObjectDescription)
    (widths : description.widthsFit = true) :
    description.symbols.cellCount < 2 ^ 32 := by
  unfold ObjectDescription.widthsFit at widths
  simp only [Bool.and_eq_true] at widths
  exact of_decide_eq_true widths.1.1.2

/-- Whole-object width validity supplies the final canonical section offset. -/
theorem ObjectDescription.widthsFit_sectionLayoutEnd
    (description : ObjectDescription)
    (widths : description.widthsFit = true) :
    description.sectionLayout.2 < 2 ^ 32 := by
  unfold ObjectDescription.widthsFit at widths
  simp only [Bool.and_eq_true] at widths
  exact of_decide_eq_true widths.1.2

/-- Synthesized object section headers all have coherent pointers. -/
theorem ObjectDescription.sectionLayout_pointersCoherent
    (description : ObjectDescription)
    (widths : description.widthsFit = true) :
    ∀ header ∈ description.sectionLayout.1.toList,
      header.PointersCoherent := by
  have endFits : 20 + 40 * description.sections.length +
      sectionDescriptionListLength description.sections.toList < 2 ^ 32 := by
    change 20 + 40 * description.sections.length +
      description.sectionsByteLength < 2 ^ 32
    rw [← description.end_sectionLayout]
    exact description.widthsFit_sectionLayoutEnd widths
  simpa only [ObjectDescription.sectionLayout, Vec.toList_fromList] using
    layoutSectionList_pointersCoherent
      (20 + 40 * description.sections.length) description.sections.toList
      (by omega) (description.widthsFit_sections widths) endFits

/-- Every canonical object section span is empty at zero or lies between the
end of the table prefix and the end of all section contents. -/
theorem ObjectDescription.sectionLayout_declaredSpan_bounds
    (description : ObjectDescription)
    (widths : description.widthsFit = true) {span : ByteSpan}
    (member : span ∈ sectionDeclaredSpans description.sectionLayout.1) :
    (span.offset = 0 ∧ span.length = 0) ∨
      (20 + 40 * description.sections.length ≤ span.offset ∧
        span.endExclusive ≤ description.sectionLayout.2) := by
  have endFits : 20 + 40 * description.sections.length +
      sectionDescriptionListLength description.sections.toList < 2 ^ 32 := by
    change 20 + 40 * description.sections.length +
      description.sectionsByteLength < 2 ^ 32
    rw [← description.end_sectionLayout]
    exact description.widthsFit_sectionLayoutEnd widths
  have rawBound := layoutSectionList_declaredSpan_bounds
    (20 + 40 * description.sections.length) description.sections.toList
    (description.widthsFit_sections widths) endFits
    (span := span) (by
      simpa only [sectionDeclaredSpans, ObjectDescription.sectionLayout,
        Vec.toList_fromList] using member)
  rcases rawBound with empty | bounded
  · exact Or.inl empty
  · right
    refine ⟨bounded.1, ?_⟩
    rw [description.end_sectionLayout]
    exact bounded.2

/-- All section spans in a width-valid canonical object are pairwise disjoint. -/
theorem ObjectDescription.sectionLayout_declaredSpans_pairwise
    (description : ObjectDescription)
    (widths : description.widthsFit = true) :
    (sectionDeclaredSpans description.sectionLayout.1).Pairwise
      ByteSpan.Disjoint := by
  have endFits : 20 + 40 * description.sections.length +
      sectionDescriptionListLength description.sections.toList < 2 ^ 32 := by
    change 20 + 40 * description.sections.length +
      description.sectionsByteLength < 2 ^ 32
    rw [← description.end_sectionLayout]
    exact description.widthsFit_sectionLayoutEnd widths
  simpa only [sectionDeclaredSpans, ObjectDescription.sectionLayout,
    Vec.toList_fromList] using
    layoutSectionList_declaredSpans_pairwise
      (20 + 40 * description.sections.length) description.sections.toList
      (description.widthsFit_sections widths) endFits

/-- Writable descriptions necessarily satisfy the complete width check. -/
theorem ObjectDescription.Writable.widthsFit
    (description : ObjectDescription)
    (writable : description.Writable = true) :
    description.widthsFit = true := by
  unfold ObjectDescription.Writable at writable
  simp only [Bool.and_eq_true] at writable
  exact writable.1

/-- Canonical optional symbol tail indexed by the synthesized file header. -/
def ObjectDescription.symbolTail (description : ObjectDescription)
    (writable : description.Writable = true) : SymbolTail description.header :=
  let widths := ObjectDescription.Writable.widthsFit description writable
  match symbolsEq : description.symbols with
  | .absent =>
    .absent (description.header_pointerToSymbolTable_absent symbolsEq)
      (by
        rw [description.header_numberOfSymbols
          (description.widthsFit_symbolCount widths)]
        simp [SymbolDescription.cellCount, symbolsEq])
  | .present cells strings =>
    have validations :
        validAuxLayoutScan cells.length cells.toList = true ∧
          validPrimaryNamesScan cells.length cells.toList strings = true := by
      unfold ObjectDescription.Writable at writable
      rw [widths, symbolsEq] at writable
      simpa only [true_and, Bool.and_eq_true] using writable
    have cellCount :
        cells.length = description.header.numberOfSymbols.toNat := by
      symm
      rw [description.header_numberOfSymbols
        (description.widthsFit_symbolCount widths)]
      simp [SymbolDescription.cellCount, symbolsEq]
    let table : SymbolTable description.header :=
      { cells, cellCount }
    let validated : AuxValidatedSymbolTable description.header :=
      { table, auxLayoutValid := validations.1 }
    have layoutFits : description.sectionLayout.2 < 2 ^ 32 := by
      unfold ObjectDescription.widthsFit at widths
      simp only [Bool.and_eq_true] at widths
      exact of_decide_eq_true widths.1.2
    have pointerNonzero :
        description.header.pointerToSymbolTable.toNat ≠ 0 := by
      rw [description.header_pointerToSymbolTable_present cells strings
        symbolsEq layoutFits]
      rw [description.end_sectionLayout]
      omega
    .present pointerNonzero validated strings validations.2

/-- The canonical object bytes drive the symbol-tail reader to the exact
proof-indexed optional tail constructed from a writable description. -/
theorem ObjectDescription.readSymbolTail_bytes
    (description : ObjectDescription)
    (writable : description.Writable = true) :
    readSymbolTail description.header description.bytes =
      .done (description.symbolTail writable) Vec.empty := by
  have widths := ObjectDescription.Writable.widthsFit description writable
  cases symbolsEq : description.symbols with
  | absent =>
      have pointerZero :=
        description.header_pointerToSymbolTable_absent symbolsEq
      have countZero : description.header.numberOfSymbols.toNat = 0 := by
        rw [description.header_numberOfSymbols
          (description.widthsFit_symbolCount widths)]
        simp [SymbolDescription.cellCount, symbolsEq]
      have tailEq : description.symbolTail writable =
          .absent pointerZero countZero := by
        unfold ObjectDescription.symbolTail
        split <;> simp_all <;> rfl
      rw [tailEq]
      exact readSymbolTail_absent description.header description.bytes
        pointerZero countZero
  | present cells strings =>
      have validations :
          validAuxLayoutScan cells.length cells.toList = true ∧
            validPrimaryNamesScan cells.length cells.toList strings = true := by
        unfold ObjectDescription.Writable at writable
        rw [widths, symbolsEq] at writable
        simpa only [true_and, Bool.and_eq_true] using writable
      have cellCount :
          cells.length = description.header.numberOfSymbols.toNat := by
        symm
        rw [description.header_numberOfSymbols
          (description.widthsFit_symbolCount widths)]
        simp [SymbolDescription.cellCount, symbolsEq]
      let table : SymbolTable description.header := { cells, cellCount }
      let validated : AuxValidatedSymbolTable description.header :=
        { table, auxLayoutValid := validations.1 }
      have layoutFits : description.sectionLayout.2 < 2 ^ 32 := by
        unfold ObjectDescription.widthsFit at widths
        simp only [Bool.and_eq_true] at widths
        exact of_decide_eq_true widths.1.2
      have pointerEq : description.header.pointerToSymbolTable.toNat =
          description.sectionLayout.2 :=
        description.header_pointerToSymbolTable_present cells strings symbolsEq
          layoutFits
      have pointerNonzero :
          description.header.pointerToSymbolTable.toNat ≠ 0 := by
        rw [pointerEq, description.end_sectionLayout]
        omega
      let contentPrefix :=
        writeHeader description.header ++
          writeSectionHeaders description.sectionLayout.1 ++
          writeSectionDescriptionList description.sections.toList
      have contentPrefixLength : contentPrefix.length =
          description.sectionLayout.2 := by
        rw [description.end_sectionLayout]
        simp [contentPrefix, ObjectDescription.sectionsByteLength,
          length_writeSectionDescriptionList]
      have bytesEq : description.bytes =
          contentPrefix ++
            (writeSymbolCells cells ++ writeStringTable strings) := by
        simp [ObjectDescription.bytes, contentPrefix, symbolsEq,
          writeSymbolDescription, Vec.append_assoc]
      have regionAt :
          description.bytes.drop
              description.header.pointerToSymbolTable.toNat =
            writeAuxValidatedSymbolTable validated ++
              writeStringTable strings := by
        rw [bytesEq, pointerEq]
        rw [Vec.drop_append_of_length_eq contentPrefixLength]
        rfl
      have minimumFits :
          description.header.symbolTableSpan.endExclusive + 4 ≤
            description.bytes.length := by
        have minimumSize := strings.minimumSize
        rw [bytesEq]
        simp [Header.symbolTableSpan, ByteSpan.endExclusive, pointerEq,
          contentPrefixLength, cellCount]
        omega
      have parsed := readSymbolTail_present_of_region description.header
        description.bytes validated strings pointerNonzero validations.2
        minimumFits regionAt
      have tailEq : description.symbolTail writable =
          .present pointerNonzero validated strings validations.2 := by
        unfold ObjectDescription.symbolTail
        split <;> simp_all <;> rfl
      rw [tailEq]
      exact parsed

/-- The synthesized prefix span ends exactly where canonical section contents
begin. -/
theorem ObjectDescription.prefixSpan_endExclusive
    (description : ObjectDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    description.header.prefixSpan.endExclusive =
      20 + 40 * description.sections.length := by
  simp [Header.prefixSpan, ByteSpan.endExclusive,
    description.header_numberOfSections sectionCountFits,
    description.header_sizeOfOptionalHeader]

/-- The end of canonical section contents never exceeds the serialized object
length; any symbol/string tail follows it. -/
theorem ObjectDescription.sectionLayoutEnd_le_length_bytes
    (description : ObjectDescription) :
    description.sectionLayout.2 ≤ description.bytes.length := by
  rw [description.length_bytes, description.end_sectionLayout]
  unfold ObjectDescription.byteLength
  omega

/-- Every writable canonical object has a coherent, bounded, pairwise-disjoint
declared span layout, including either form of the optional symbol tail. -/
theorem ObjectDescription.layoutValid (description : ObjectDescription)
    (writable : description.Writable = true) :
    DeclaredObjectLayoutValid description.header description.sectionLayout.1
      (description.symbolTail writable).stringTable? description.bytes.length := by
  have widths := ObjectDescription.Writable.widthsFit description writable
  have sectionCountFits := description.widthsFit_sectionCount widths
  have sectionCount : description.sectionLayout.1.length =
      description.header.numberOfSections.toNat := by
    rw [description.length_sectionLayout]
    symm
    exact description.header_numberOfSections sectionCountFits
  have sectionPointers := description.sectionLayout_pointersCoherent widths
  have sectionPairwise :=
    description.sectionLayout_declaredSpans_pairwise widths
  have prefixEnd := description.prefixSpan_endExclusive sectionCountFits
  have layoutEndLeBytes := description.sectionLayoutEnd_le_length_bytes
  have prefixSectionFits : ∀ span ∈
      description.header.prefixSpan ::
        sectionDeclaredSpans description.sectionLayout.1,
      span.Fits description.bytes.length := by
    intro span member
    simp only [List.mem_cons] at member
    rcases member with rfl | sectionMember
    · unfold ByteSpan.Fits
      rw [prefixEnd]
      exact Nat.le_trans (by
        rw [description.end_sectionLayout]
        omega) layoutEndLeBytes
    · rcases description.sectionLayout_declaredSpan_bounds widths
          sectionMember with empty | bounded
      · unfold ByteSpan.Fits ByteSpan.endExclusive
        omega
      · exact Nat.le_trans bounded.2 layoutEndLeBytes
  have prefixSectionPairwise :
      (description.header.prefixSpan ::
        sectionDeclaredSpans description.sectionLayout.1).Pairwise
          ByteSpan.Disjoint := by
    apply List.Pairwise.cons
    · intro span member
      rcases description.sectionLayout_declaredSpan_bounds widths member with
        empty | bounded
      · right
        unfold Header.prefixSpan ByteSpan.endExclusive
        omega
      · left
        rw [prefixEnd]
        exact bounded.1
    · exact sectionPairwise
  cases symbolsEq : description.symbols with
  | absent =>
      have pointerZero :=
        description.header_pointerToSymbolTable_absent symbolsEq
      have countZero : description.header.numberOfSymbols.toNat = 0 := by
        rw [description.header_numberOfSymbols
          (description.widthsFit_symbolCount widths)]
        simp [SymbolDescription.cellCount, symbolsEq]
      have tailEq : description.symbolTail writable =
          .absent pointerZero countZero := by
        unfold ObjectDescription.symbolTail
        split <;> simp_all <;> rfl
      have stringsEq :
          (description.symbolTail writable).stringTable? = none := by
        rw [tailEq]
        rfl
      rw [stringsEq]
      refine ⟨sectionCount, ?_, sectionPointers, ?_, ?_⟩
      · exact ⟨pointerZero, countZero⟩
      · simpa [declaredObjectSpans] using prefixSectionFits
      · simpa [declaredObjectSpans] using prefixSectionPairwise
  | present cells strings =>
      have layoutFits := description.widthsFit_sectionLayoutEnd widths
      have pointerEq : description.header.pointerToSymbolTable.toNat =
          description.sectionLayout.2 :=
        description.header_pointerToSymbolTable_present cells strings symbolsEq
          layoutFits
      have pointerNonzero :
          description.header.pointerToSymbolTable.toNat ≠ 0 := by
        rw [pointerEq, description.end_sectionLayout]
        omega
      have countEq : description.header.numberOfSymbols.toNat = cells.length := by
        rw [description.header_numberOfSymbols
          (description.widthsFit_symbolCount widths)]
        simp [SymbolDescription.cellCount, symbolsEq]
      have validations :
          validAuxLayoutScan cells.length cells.toList = true ∧
            validPrimaryNamesScan cells.length cells.toList strings = true := by
        unfold ObjectDescription.Writable at writable
        rw [widths, symbolsEq] at writable
        simpa only [true_and, Bool.and_eq_true] using writable
      have cellCount :
          cells.length = description.header.numberOfSymbols.toNat :=
        countEq.symm
      let table : SymbolTable description.header := { cells, cellCount }
      let validated : AuxValidatedSymbolTable description.header :=
        { table, auxLayoutValid := validations.1 }
      have tailEq : description.symbolTail writable =
          .present pointerNonzero validated strings validations.2 := by
        unfold ObjectDescription.symbolTail
        split <;> simp_all <;> rfl
      have bytesLength : description.bytes.length =
          description.sectionLayout.2 + 18 * cells.length +
            strings.declaredSize.toNat := by
        rw [description.length_bytes, description.end_sectionLayout]
        unfold ObjectDescription.byteLength
        simp [SymbolDescription.byteLength, symbolsEq]
        omega
      have stringsEq :
          (description.symbolTail writable).stringTable? = some strings := by
        rw [tailEq]
        rfl
      rw [stringsEq]
      refine ⟨sectionCount, pointerNonzero, sectionPointers, ?_, ?_⟩
      · intro span member
        simp [declaredObjectSpans] at member
        rcases member with rfl | prefixOrSection | rfl | rfl
        · exact prefixSectionFits description.header.prefixSpan (by simp)
        · exact prefixSectionFits span (by simp [prefixOrSection])
        · simp [ByteSpan.Fits, Header.symbolTableSpan,
            ByteSpan.endExclusive, pointerEq, countEq, bytesLength]
        · simp [ByteSpan.Fits, Header.stringTableSpan,
            Header.symbolTableSpan, ByteSpan.endExclusive, pointerEq, countEq,
            bytesLength]
      · change (description.header.prefixSpan ::
          sectionDeclaredSpans description.sectionLayout.1 ++
          [description.header.symbolTableSpan,
            description.header.stringTableSpan strings]).Pairwise
            ByteSpan.Disjoint
        rw [List.pairwise_append]
        refine ⟨prefixSectionPairwise, ?_, ?_⟩
        · simp [ByteSpan.Disjoint, Header.symbolTableSpan,
            Header.stringTableSpan, ByteSpan.endExclusive, pointerEq, countEq]
        · intro left leftMember right rightMember
          have leftEnd : left.endExclusive ≤ description.sectionLayout.2 := by
            simp only [List.mem_cons] at leftMember
            rcases leftMember with rfl | sectionMember
            · rw [prefixEnd, description.end_sectionLayout]
              omega
            · rcases description.sectionLayout_declaredSpan_bounds widths
                  sectionMember with empty | bounded
              · unfold ByteSpan.endExclusive
                omega
              · exact bounded.2
          have rightOffset : description.sectionLayout.2 ≤ right.offset := by
            simp at rightMember
            rcases rightMember with rfl | rfl
            · simp [Header.symbolTableSpan, pointerEq]
            · simp [Header.stringTableSpan, Header.symbolTableSpan,
                ByteSpan.endExclusive, pointerEq]
          left
          exact Nat.le_trans leftEnd rightOffset

/-- Canonical dependent contents corresponding to an object description's
synthesized section layout. -/
def ObjectDescription.contents (description : ObjectDescription)
    (widths : description.widthsFit = true) : Vec SectionContents :=
  Vec.fromList (sectionContentsListAt
    (20 + 40 * description.sections.length) description.sections.toList
    (description.widthsFit_sections widths))

/-- Canonical object contents retain exactly the synthesized section headers. -/
theorem ObjectDescription.contents_headers (description : ObjectDescription)
    (widths : description.widthsFit = true) :
    (description.contents widths).map SectionContents.header =
      description.sectionLayout.1 := by
  apply Vec.toList_injective
  change (sectionContentsListAt (20 + 40 * description.sections.length)
      description.sections.toList
      (description.widthsFit_sections widths)).map SectionContents.header =
    (layoutSectionList (20 + 40 * description.sections.length)
      description.sections.toList).1
  exact sectionContentsListAt_headers _ _ _

/-- The section-list phase of the object reader recovers every canonical
dependent section content from the object's serialized bytes. -/
theorem ObjectDescription.readSectionContentsList_bytes
    (description : ObjectDescription)
    (widths : description.widthsFit = true) :
    readSectionContentsList description.sectionLayout.1.toList
        description.bytes =
      .done (description.contents widths).toList Vec.empty := by
  have sectionWidths := description.widthsFit_sections widths
  have prefixLength :
      (writeHeader description.header ++
        writeSectionHeaders description.sectionLayout.1).length =
        20 + 40 * description.sections.length := by
    simp
  have layoutEndFits : description.sectionLayout.2 < 2 ^ 32 := by
    unfold ObjectDescription.widthsFit at widths
    simp only [Bool.and_eq_true] at widths
    exact of_decide_eq_true widths.1.2
  have contentEndFits :
      20 + 40 * description.sections.length +
        sectionDescriptionListLength description.sections.toList < 2 ^ 32 := by
    change 20 + 40 * description.sections.length +
      description.sectionsByteLength < 2 ^ 32
    rw [← description.end_sectionLayout]
    exact layoutEndFits
  have parsed := readSectionContentsList_writeSectionDescriptionList_append
    description.sections.toList
    (20 + 40 * description.sections.length)
    (writeHeader description.header ++
      writeSectionHeaders description.sectionLayout.1)
    (writeSymbolDescription description.symbols) prefixLength sectionWidths
    contentEndFits
  simpa only [ObjectDescription.sectionLayout, ObjectDescription.bytes,
    ObjectDescription.contents, Vec.toList_fromList, Vec.append_assoc] using
    parsed

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
