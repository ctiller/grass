import Grass.Artifact.PE.Image

/-!
# Canonical PE32+ image writer

`ImageDescription.bytes` consumes raw image and section descriptions and
synthesizes the COFF section count, file pointers, and aligned bytes.
`ImageDescription.Writable` rejects layouts that cannot be represented by the
PE fields. The input remains a low-level layout description rather than a
high-level program specification.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

/-- Round `value` upward to the next `alignment` boundary. A zero alignment is
left unchanged and is rejected by `ImageDescription.Writable`. -/
def alignUp (value alignment : Nat) : Nat :=
  if value % alignment = 0 then value
  else value + (alignment - value % alignment)

/-- Alignment rounding never moves a value backward. -/
theorem le_alignUp (value alignment : Nat) : value ≤ alignUp value alignment := by
  unfold alignUp
  split <;> omega

/-- Rounding by a positive alignment produces an exact alignment boundary. -/
theorem alignUp_mod_eq_zero (value : Nat) {alignment : Nat}
    (positive : 0 < alignment) : alignUp value alignment % alignment = 0 := by
  unfold alignUp
  split
  next aligned => exact aligned
  next unaligned =>
    rw [Nat.add_mod]
    have remainderLt : value % alignment < alignment :=
      Nat.mod_lt value positive
    rw [Nat.mod_eq_of_lt (by omega : alignment - value % alignment < alignment)]
    have fillsBoundary :
        value % alignment + (alignment - value % alignment) = alignment := by
      omega
    rw [fillsBoundary, Nat.mod_self]

/-- Append the canonical zero padding required to reach an alignment boundary. -/
def padBytes (alignment : Nat) (bytes : Std.Logical.ByteArray) :
    Std.Logical.ByteArray :=
  bytes ++ Vec.replicate (alignUp bytes.length alignment - bytes.length) 0

/-- `length_padBytes` exposes the exact aligned byte length. -/
@[simp] theorem length_padBytes (alignment : Nat)
    (bytes : Std.Logical.ByteArray) :
    (padBytes alignment bytes).length = alignUp bytes.length alignment := by
  simp [padBytes]
  have bounded := le_alignUp bytes.length alignment
  omega

/-- Raw fields and payload supplied for one canonical PE image section. -/
structure ImageSectionDescription where
  name : SizedByteArray 8
  virtualSize : BitVec 32
  virtualAddress : BitVec 32
  rawData : Std.Logical.ByteArray
  characteristics : BitVec 32
deriving DecidableEq, Repr

/-- The payload bytes after canonical file-alignment padding. -/
def ImageSectionDescription.paddedRawData
    (description : ImageSectionDescription) (alignment : Nat) :
    Std.Logical.ByteArray :=
  padBytes alignment description.rawData

/-- Use zero for an empty extent and its canonical offset otherwise. -/
private def rawDataPointer (offset length : Nat) : BitVec 32 :=
  if length = 0 then 0 else BitVec.ofNat 32 offset

/-- Synthesize one image section header at its assigned file offset. -/
def ImageSectionDescription.headerAt
    (description : ImageSectionDescription) (alignment offset : Nat) :
    SectionHeader :=
  let payloadLength := alignUp description.rawData.length alignment
  { name := description.name
    physicalAddressOrVirtualSize := description.virtualSize
    virtualAddress := description.virtualAddress
    sizeOfRawData := BitVec.ofNat 32 payloadLength
    pointerToRawData := rawDataPointer offset payloadLength
    pointerToRelocations := 0
    pointerToLineNumbers := 0
    numberOfRelocations := 0
    numberOfLineNumbers := 0
    characteristics := description.characteristics }

/-- A representable nonempty payload records its assigned raw-data offset. -/
@[simp] theorem ImageSectionDescription.headerAt_pointerToRawData
    (description : ImageSectionDescription) (alignment offset : Nat)
    (nonempty : (description.paddedRawData alignment).length ≠ 0)
    (offsetFits : offset < 2 ^ 32) :
    (description.headerAt alignment offset).pointerToRawData.toNat = offset := by
  rw [ImageSectionDescription.paddedRawData, length_padBytes] at nonempty
  simp [ImageSectionDescription.headerAt, rawDataPointer, nonempty,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetFits]

/-- A representable payload records its canonically padded byte length. -/
@[simp] theorem ImageSectionDescription.headerAt_sizeOfRawData
    (description : ImageSectionDescription) (alignment offset : Nat)
    (lengthFits : (description.paddedRawData alignment).length < 2 ^ 32) :
    (description.headerAt alignment offset).sizeOfRawData.toNat =
      (description.paddedRawData alignment).length := by
  rw [ImageSectionDescription.paddedRawData, length_padBytes] at lengthFits ⊢
  simp [ImageSectionDescription.headerAt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt lengthFits]

/-- A representable synthesized section header has coherent PE-only pointer
fields, including the canonical zero pointer for an empty payload. -/
theorem ImageSectionDescription.headerAt_imageSectionPointersCoherent
    (description : ImageSectionDescription) (alignment offset : Nat)
    (offsetPositive : 0 < offset)
    (lengthFits : alignUp description.rawData.length alignment < 2 ^ 32)
    (extentFits : alignUp description.rawData.length alignment = 0 ∨
      offset + alignUp description.rawData.length alignment < 2 ^ 32) :
    imageSectionPointersCoherent (description.headerAt alignment offset) := by
  let length := alignUp description.rawData.length alignment
  unfold imageSectionPointersCoherent SectionHeader.rawDataSpan
    ByteSpan.PointerCoherent
  simp only [ImageSectionDescription.headerAt]
  change
    ((rawDataPointer offset length).toNat = 0 ↔
      (BitVec.ofNat 32 length).toNat = 0) ∧
    (0 : BitVec 32).toNat = 0 ∧
    (0 : BitVec 16).toNat = 0 ∧
    (0 : BitVec 32).toNat = 0 ∧
    (0 : BitVec 16).toNat = 0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthFits]
  unfold rawDataPointer
  split
  next empty => simpa [length] using empty
  next nonempty =>
    have offsetFits : offset < 2 ^ 32 := by
      rcases extentFits with empty | fits
      · contradiction
      · omega
    have offsetNonzero : offset ≠ 0 := by omega
    have lengthNonzero :
        alignUp description.rawData.length alignment ≠ 0 := by
      simpa [length] using nonempty
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetFits]
    simp [offsetNonzero, lengthNonzero]

/-- The raw-data span of a representable synthesized header is its assigned
interval, with the canonical zero span for an empty payload. -/
theorem ImageSectionDescription.headerAt_rawDataSpan
    (description : ImageSectionDescription) (alignment offset : Nat)
    (lengthFits : alignUp description.rawData.length alignment < 2 ^ 32)
    (extentFits : alignUp description.rawData.length alignment = 0 ∨
      offset + alignUp description.rawData.length alignment < 2 ^ 32) :
    (description.headerAt alignment offset).rawDataSpan =
      if alignUp description.rawData.length alignment = 0 then
        { offset := 0, length := 0 }
      else
        { offset := offset,
          length := alignUp description.rawData.length alignment } := by
  unfold SectionHeader.rawDataSpan ImageSectionDescription.headerAt
  split
  next empty =>
    simp [rawDataPointer, empty]
  next nonempty =>
    have offsetFits : offset < 2 ^ 32 := by
      rcases extentFits with empty | fits
      · contradiction
      · omega
    congr 1 <;>
      simp [rawDataPointer, nonempty, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt offsetFits, Nat.mod_eq_of_lt lengthFits]

/-- Lay out section headers consecutively from an aligned starting offset. -/
def layoutImageSectionList (alignment : Nat) :
    Nat → List ImageSectionDescription → List SectionHeader × Nat
  | offset, [] => ([], offset)
  | offset, description :: descriptions =>
    let payloadLength := alignUp description.rawData.length alignment
    let header := description.headerAt alignment offset
    let tail := layoutImageSectionList alignment
      (offset + payloadLength) descriptions
    (header :: tail.1, tail.2)

/-- `layoutImageSectionList` emits one header per source description. -/
theorem length_layoutImageSectionList (alignment offset : Nat)
    (descriptions : List ImageSectionDescription) :
    (layoutImageSectionList alignment offset descriptions).1.length =
      descriptions.length := by
  induction descriptions generalizing offset with
  | nil => rfl
  | cons description descriptions ih =>
      simp [layoutImageSectionList, ih]

/-- A singleton image layout emits exactly the header at its starting offset. -/
@[simp] theorem layoutImageSectionList_singleton (alignment offset : Nat)
    (description : ImageSectionDescription) :
    (layoutImageSectionList alignment offset [description]).1 =
      [description.headerAt alignment offset] := by
  rfl

/-- Serialize canonically padded section payloads in source order. -/
def writeImageSectionDescriptionList (alignment : Nat) :
    List ImageSectionDescription → Std.Logical.ByteArray
  | [] => Vec.empty
  | description :: descriptions =>
    description.paddedRawData alignment ++
      writeImageSectionDescriptionList alignment descriptions

/-- A singleton payload list serializes to that payload's padded bytes. -/
@[simp] theorem writeImageSectionDescriptionList_singleton
    (alignment : Nat) (description : ImageSectionDescription) :
    writeImageSectionDescriptionList alignment [description] =
      description.paddedRawData alignment := by
  simp [writeImageSectionDescriptionList]

/-- Raw low-level input accepted by the canonical image writer. -/
structure ImageDescription where
  machine : BitVec 16
  timeDateStamp : BitVec 32
  characteristics : BitVec 16
  optionalHeader : OptionalHeader
  sections : Vec ImageSectionDescription
deriving DecidableEq, Repr

/-- File alignment declared by the supplied optional header. -/
def ImageDescription.fileAlignment (description : ImageDescription) : Nat :=
  description.optionalHeader.windowsPrefix.fileAlignment.toNat

/-- Serialized header/table width before file-alignment padding. -/
def ImageDescription.unalignedHeaderSize (description : ImageDescription) : Nat :=
  264 + 40 * description.sections.length

/-- First possible raw-data byte after aligning the synthesized headers. -/
def ImageDescription.firstRawDataOffset
    (description : ImageDescription) : Nat :=
  alignUp description.unalignedHeaderSize description.fileAlignment

/-- Canonically synthesized section headers and the exclusive payload end. -/
def ImageDescription.sectionLayout (description : ImageDescription) :
    Vec SectionHeader × Nat :=
  let layout := layoutImageSectionList description.fileAlignment
    description.firstRawDataOffset description.sections.toList
  (Vec.fromList layout.1, layout.2)

/-- Synthesized section headers retain the description count exactly. -/
@[simp] theorem ImageDescription.length_sectionLayout
    (description : ImageDescription) :
    description.sectionLayout.1.length = description.sections.length := by
  change (layoutImageSectionList description.fileAlignment
    description.firstRawDataOffset description.sections.toList).1.length =
      description.sections.toList.length
  exact length_layoutImageSectionList _ _ _

/-- Update only the synthesized header-byte extent in an optional header. -/
def OptionalHeader.withSizeOfHeaders (header : OptionalHeader)
    (size : Nat) : OptionalHeader :=
  { header with imageFields :=
      { header.imageFields with sizeOfHeaders := BitVec.ofNat 32 size } }

/-- Synthesize canonical image headers from a representable section count. -/
def ImageDescription.imageHeaders (description : ImageDescription) :
    ImageHeaders :=
  let optionalHeader := description.optionalHeader.withSizeOfHeaders
    description.firstRawDataOffset
  let fileHeader : Header :=
    { machine := description.machine
      numberOfSections := BitVec.ofNat 16 description.sections.length
      timeDateStamp := description.timeDateStamp
      pointerToSymbolTable := 0
      numberOfSymbols := 0
      sizeOfOptionalHeader := 240
      characteristics := description.characteristics }
  { headerPrefix := ⟨fileHeader⟩
    optionalHeader := optionalHeader
    optionalHeaderSize := by
      change (240 : BitVec 16).toNat = 240
      decide }

/-- Assemble the typed header and section-table value. -/
def ImageDescription.imageSectionTable (description : ImageDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    ImageSectionTable :=
  { headers := description.imageHeaders
    sections := description.sectionLayout.1
    sectionCount := by
      rw [description.length_sectionLayout]
      simp [ImageDescription.imageHeaders, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt sectionCountFits] }

/-- Every synthesized section placement fits in its 32-bit size and offset
fields. Empty payloads need no file pointer. -/
def imageSectionPlacementsFit (alignment : Nat) :
    Nat → List ImageSectionDescription → Bool
  | _, [] => true
  | offset, description :: descriptions =>
    let length := alignUp description.rawData.length alignment
    decide (length < 2 ^ 32) &&
    decide (length = 0 ∨ offset + length < 2 ^ 32) &&
    imageSectionPlacementsFit alignment (offset + length) descriptions

/-- Complete arithmetic obligations required by the canonical writer. -/
def ImageDescription.Writable (description : ImageDescription) : Prop :=
  0 < description.fileAlignment ∧
  description.sections.length < 2 ^ 16 ∧
  description.firstRawDataOffset < 2 ^ 32 ∧
  imageSectionPlacementsFit description.fileAlignment
    description.firstRawDataOffset description.sections.toList = true

instance (description : ImageDescription) :
    Decidable description.Writable := by
  unfold ImageDescription.Writable
  infer_instance

/-- Canonical bytes synthesized from a description with a representable count. -/
def ImageDescription.bytes (description : ImageDescription)
    (sectionCountFits : description.sections.length < 2 ^ 16) :
    Std.Logical.ByteArray :=
  let table := description.imageSectionTable sectionCountFits
  let headerBytes := writeImageSectionTable table
  headerBytes ++
    Vec.replicate
      (description.firstRawDataOffset - headerBytes.length) 0 ++
    writeImageSectionDescriptionList description.fileAlignment
      description.sections.toList

/-- Emit canonical image bytes or reject an unrepresentable description. -/
def writeImageDescription (description : ImageDescription) :
    Except ParseError Std.Logical.ByteArray :=
  if writable : description.Writable then
    .ok (description.bytes writable.2.1)
  else
    .error (.arithmeticOverflow
      "PE32+ image layout exceeds field width or has zero file alignment")

/-- Every successful write returns bytes synthesized from a complete proof of
the writer's arithmetic obligations. -/
theorem writeImageDescription_ok {description : ImageDescription}
    {bytes : Std.Logical.ByteArray}
    (success : writeImageDescription description = .ok bytes) :
    ∃ writable : description.Writable,
      bytes = description.bytes writable.2.1 := by
  unfold writeImageDescription at success
  split at success <;> try contradiction
  next writable =>
    injection success with bytesEq
    exact ⟨writable, bytesEq.symm⟩

end Grass.Artifact.PE
