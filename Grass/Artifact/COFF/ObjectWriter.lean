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

/-- Serialize an optional symbol/string-table tail. -/
def writeSymbolDescription : SymbolDescription → Std.Logical.ByteArray
  | .absent => Vec.empty
  | .present cells strings => writeSymbolCells cells ++ writeStringTable strings

/-- Serialized width of an optional symbol/string-table tail. -/
def SymbolDescription.byteLength : SymbolDescription → Nat
  | .absent => 0
  | .present cells strings => 18 * cells.length + strings.declaredSize.toNat

/-- Closed-form length of the canonical object serialization. -/
def ObjectDescription.byteLength (description : ObjectDescription) : Nat :=
  20 + 40 * description.sections.length +
    sectionDescriptionListLength description.sections.toList +
    description.symbols.byteLength

/-- Unchecked canonical bytes after all derived pointers have been synthesized. -/
def ObjectDescription.bytes (description : ObjectDescription) :
    Std.Logical.ByteArray :=
  let layout := description.sectionLayout
  writeHeader description.header ++ writeSectionHeaders layout.1 ++
    writeSectionDescriptionList description.sections.toList ++
    writeSymbolDescription description.symbols

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

end Grass.Artifact.COFF
