import Grass.Artifact.COFF.Header

/-!
# COFF section header

This module models the fixed 40-byte section-table entry shared by COFF object
files and PE images. It deliberately retains the format's raw numeric fields;
relocation meaning, image layout policy, and section-permission legality belong
to later contextual validation.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- The ten fields of a COFF section-table entry. `name` retains all eight
bytes, including padding or the slash-prefixed string-table representation. -/
structure SectionHeader where
  name : SizedByteArray 8
  physicalAddressOrVirtualSize : BitVec 32
  virtualAddress : BitVec 32
  sizeOfRawData : BitVec 32
  pointerToRawData : BitVec 32
  pointerToRelocations : BitVec 32
  pointerToLineNumbers : BitVec 32
  numberOfRelocations : BitVec 16
  numberOfLineNumbers : BitVec 16
  characteristics : BitVec 32
deriving DecidableEq, Repr

/-- Product shape consumed directly by the generic grammar combinators. -/
abbrev SectionHeaderFields :=
  SizedByteArray 8 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
    BitVec 32 × BitVec 32 × BitVec 16 × BitVec 16 × BitVec 32

/-- Forget field labels while retaining every fixed-width value. -/
def SectionHeader.toFields (entry : SectionHeader) : SectionHeaderFields :=
  (entry.name, entry.physicalAddressOrVirtualSize, entry.virtualAddress,
    entry.sizeOfRawData, entry.pointerToRawData,
    entry.pointerToRelocations, entry.pointerToLineNumbers,
    entry.numberOfRelocations, entry.numberOfLineNumbers,
    entry.characteristics)

/-- Restore a named section-table entry from its grammar product. -/
def SectionHeader.ofFields (fields : SectionHeaderFields) : SectionHeader :=
  { name := fields.1
    physicalAddressOrVirtualSize := fields.2.1
    virtualAddress := fields.2.2.1
    sizeOfRawData := fields.2.2.2.1
    pointerToRawData := fields.2.2.2.2.1
    pointerToRelocations := fields.2.2.2.2.2.1
    pointerToLineNumbers := fields.2.2.2.2.2.2.1
    numberOfRelocations := fields.2.2.2.2.2.2.2.1
    numberOfLineNumbers := fields.2.2.2.2.2.2.2.2.1
    characteristics := fields.2.2.2.2.2.2.2.2.2 }

/-- Named section headers and their grammar products are a total isomorphism. -/
def sectionHeaderFieldsIsomorphism :
    Isomorphism SectionHeaderFields SectionHeader where
  forward := SectionHeader.ofFields
  backward := SectionHeader.toFields
  backward_forward := by
    intro fields
    rcases fields with ⟨a, b, c, d, e, f, g, h, i, j⟩
    rfl
  forward_backward := by
    intro entry
    rcases entry with ⟨a, b, c, d, e, f, g, h, i, j⟩
    rfl

/-- Generic binary grammar for a COFF section-table entry. -/
def sectionHeaderFieldsFormat : Format SectionHeaderFields :=
  .seq (fixedBytesFormat 8) fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  littleEndianU32Format

/-- The typed language of a fixed-width COFF section-table entry. -/
def sectionHeaderFormat : Format SectionHeader :=
  sectionHeaderFieldsFormat.iso sectionHeaderFieldsIsomorphism

/-- Decode a section-table entry after the 40-byte bound is established. -/
private def readCompleteSectionHeader
    (input : Std.Logical.ByteArray) : ParseResult SectionHeader :=
  match takeExactSized 8 input with
  | .done name rest =>
    match takeLittleEndian 4 rest with
    | .done physicalAddressOrVirtualSize rest =>
      match takeLittleEndian 4 rest with
      | .done virtualAddress rest =>
        match takeLittleEndian 4 rest with
        | .done sizeOfRawData rest =>
          match takeLittleEndian 4 rest with
          | .done pointerToRawData rest =>
            match takeLittleEndian 4 rest with
            | .done pointerToRelocations rest =>
              match takeLittleEndian 4 rest with
              | .done pointerToLineNumbers rest =>
                match takeLittleEndian 2 rest with
                | .done numberOfRelocations rest =>
                  match takeLittleEndian 2 rest with
                  | .done numberOfLineNumbers rest =>
                    match takeLittleEndian 4 rest with
                    | .done characteristics rest => .done {
                        name, physicalAddressOrVirtualSize, virtualAddress,
                        sizeOfRawData, pointerToRawData, pointerToRelocations,
                        pointerToLineNumbers, numberOfRelocations,
                        numberOfLineNumbers, characteristics } rest
                    | .needMore hint => .needMore hint
                    | .invalid error => .invalid error
                  | .needMore hint => .needMore hint
                  | .invalid error => .invalid error
                | .needMore hint => .needMore hint
                | .invalid error => .invalid error
              | .needMore hint => .needMore hint
              | .invalid error => .invalid error
            | .needMore hint => .needMore hint
            | .invalid error => .invalid error
          | .needMore hint => .needMore hint
          | .invalid error => .invalid error
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse one fixed-width COFF section header with exact short-prefix
classification and exact preservation of following section-table bytes. -/
def readSectionHeader (input : Std.Logical.ByteArray) : ParseResult SectionHeader :=
  if 40 ≤ input.length then
    readCompleteSectionHeader input
  else
    .needMore (some (40 - input.length))

/-- `readSectionHeader_short` reports the exact number of bytes missing from a
truncated section-table entry. -/
theorem readSectionHeader_short {input : Std.Logical.ByteArray}
    (short : input.length < 40) :
    readSectionHeader input = .needMore (some (40 - input.length)) := by
  simp [readSectionHeader, Nat.not_le.mpr short]

/-- Serialize the canonical 40-byte representation of a COFF section header. -/
def writeSectionHeader (entry : SectionHeader) : Std.Logical.ByteArray :=
  writeExact entry.name ++
  writeLittleEndian (count := 4) entry.physicalAddressOrVirtualSize ++
  writeLittleEndian (count := 4) entry.virtualAddress ++
  writeLittleEndian (count := 4) entry.sizeOfRawData ++
  writeLittleEndian (count := 4) entry.pointerToRawData ++
  writeLittleEndian (count := 4) entry.pointerToRelocations ++
  writeLittleEndian (count := 4) entry.pointerToLineNumbers ++
  writeLittleEndian (count := 2) entry.numberOfRelocations ++
  writeLittleEndian (count := 2) entry.numberOfLineNumbers ++
  writeLittleEndian (count := 4) entry.characteristics

/-- `length_writeSectionHeader` fixes every serialized section-table entry at
the format-mandated width of 40 bytes. -/
@[simp] theorem length_writeSectionHeader (entry : SectionHeader) :
    (writeSectionHeader entry).length = 40 := by
  simp [writeSectionHeader, writeLittleEndian, isoWriter, writeExact]

/-- Every canonical section-header serialization derives from the declared
typed grammar. -/
theorem writeSectionHeader_derives (entry : SectionHeader) :
    Derives sectionHeaderFormat (writeSectionHeader entry) entry Vec.empty := by
  rcases entry with ⟨name, physical, address, size, raw, relocations, lines,
    relocationCount, lineCount, flags⟩
  unfold sectionHeaderFormat
  refine @Derives.iso SectionHeaderFields SectionHeader sectionHeaderFieldsFormat
    sectionHeaderFieldsIsomorphism _ Vec.empty
    (name, physical, address, size, raw, relocations, lines,
      relocationCount, lineCount, flags) ?_
  simp only [writeSectionHeader, Vec.append_assoc]
  unfold sectionHeaderFieldsFormat littleEndianU16Format littleEndianU32Format
  exact Derives.seqAppend
    ((writeExact_realizes 8).sound name)
    (Derives.seqAppend
      ((writeLittleEndian_realizes 4).sound physical)
      (Derives.seqAppend
        ((writeLittleEndian_realizes 4).sound address)
        (Derives.seqAppend
          ((writeLittleEndian_realizes 4).sound size)
          (Derives.seqAppend
            ((writeLittleEndian_realizes 4).sound raw)
            (Derives.seqAppend
              ((writeLittleEndian_realizes 4).sound relocations)
              (Derives.seqAppend
                ((writeLittleEndian_realizes 4).sound lines)
                (Derives.seqAppend
                  ((writeLittleEndian_realizes 2).sound relocationCount)
                  (Derives.seqAppend
                    ((writeLittleEndian_realizes 2).sound lineCount)
                    ((writeLittleEndian_realizes 4).sound flags)))))))))

/-- `readSectionHeader_writeSectionHeader_append` is the prefix-preserving
canonical round trip for section-table entries. -/
@[simp] theorem readSectionHeader_writeSectionHeader_append
    (entry : SectionHeader) (rest : Std.Logical.ByteArray) :
    readSectionHeader (writeSectionHeader entry ++ rest) =
      .done entry rest := by
  rcases entry with ⟨name, physical, address, size, raw, relocations, lines,
    relocationCount, lineCount, flags⟩
  simp only [readSectionHeader, Vec.length_append, length_writeSectionHeader]
  have enough : 40 ≤ 40 + rest.length := by omega
  simp only [enough, ite_true]
  simp only [readCompleteSectionHeader, writeSectionHeader, Vec.append_assoc]
  simp only [takeExactSized_writeExact_append,
    takeLittleEndian_writeLittleEndian_append]

/-- Whole-entry canonical writer/reader round trip. -/
@[simp] theorem readSectionHeader_writeSectionHeader (entry : SectionHeader) :
    readSectionHeader (writeSectionHeader entry) =
      .done entry Vec.empty := by
  simpa using readSectionHeader_writeSectionHeader_append entry Vec.empty

end Grass.Artifact.COFF
