import Grass.Artifact.COFF.Object

/-!
# Canonical COFF relocatable-object writer

The writer consumes only raw layout data: uninterpreted section bytes, raw
relocation and line-number records, raw symbol cells, and an optional parsed
string table. It derives all section counts and file pointers from canonical
contiguous placement and rejects values that do not fit their COFF fields.
-/

namespace Grass.Artifact.COFF

open Grass.Grammar Grass.Std.Logical

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

/-- Serialize one section's raw bytes, relocations, and line numbers in order. -/
def writeSectionDescription (description : SectionDescription) :
    Std.Logical.ByteArray :=
  description.rawData ++ writeRelocations description.relocations ++
    writeLineNumbers description.lineNumbers

/-- `length_writeSectionDescription` agrees with the closed-form section width. -/
@[simp] theorem length_writeSectionDescription (description : SectionDescription) :
    (writeSectionDescription description).length = description.byteLength := by
  simp [writeSectionDescription, SectionDescription.byteLength, Nat.add_assoc]

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
