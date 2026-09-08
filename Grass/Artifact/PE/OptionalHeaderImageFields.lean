import Grass.Artifact.PE.OptionalHeaderVersions

/-!
# PE32+ optional-header image fields

This module models the four 32-bit quantities following the PE version block:
the reserved Win32 value, image extent, header extent, and checksum. Their
cross-field and loader-policy constraints remain separate validation layers.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Raw image extent and checksum fields in PE binary order. -/
structure OptionalHeaderImageFields where
  win32VersionValue : BitVec 32
  sizeOfImage : BitVec 32
  sizeOfHeaders : BitVec 32
  checkSum : BitVec 32
deriving DecidableEq, Repr

/-- Product shape consumed by the generic sequencing grammar. -/
abbrev OptionalHeaderImageFieldProduct :=
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- Forget field labels while preserving PE binary order. -/
def OptionalHeaderImageFields.toProduct
    (fields : OptionalHeaderImageFields) : OptionalHeaderImageFieldProduct :=
  (fields.win32VersionValue, fields.sizeOfImage,
    fields.sizeOfHeaders, fields.checkSum)

/-- Restore named image fields from their grammar product. -/
def OptionalHeaderImageFields.ofProduct
    (fields : OptionalHeaderImageFieldProduct) :
    OptionalHeaderImageFields :=
  ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩

/-- Named image fields and their grammar products are totally isomorphic. -/
def optionalHeaderImageFieldIsomorphism :
    Isomorphism OptionalHeaderImageFieldProduct OptionalHeaderImageFields where
  forward := OptionalHeaderImageFields.ofProduct
  backward := OptionalHeaderImageFields.toProduct
  backward_forward := by
    intro fields
    rcases fields with ⟨reserved, imageSize, headerSize, checksum⟩
    rfl
  forward_backward := by
    intro fields
    rcases fields with ⟨reserved, imageSize, headerSize, checksum⟩
    rfl

/-- Generic grammar for the four little-endian image quantities. -/
def optionalHeaderImageFieldProductFormat :
    Format OptionalHeaderImageFieldProduct :=
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  littleEndianU32Format

/-- Typed language of the 16-byte optional-header image-field block. -/
def optionalHeaderImageFieldsFormat : Format OptionalHeaderImageFields :=
  optionalHeaderImageFieldProductFormat.iso
    optionalHeaderImageFieldIsomorphism

/-- Decode image fields after establishing their complete 16-byte extent. -/
private def readCompleteOptionalHeaderImageFields
    (input : Std.Logical.ByteArray) : ParseResult OptionalHeaderImageFields :=
  match takeLittleEndian 4 input with
  | .done win32VersionValue rest =>
    match takeLittleEndian 4 rest with
    | .done sizeOfImage rest =>
      match takeLittleEndian 4 rest with
      | .done sizeOfHeaders rest =>
        match takeLittleEndian 4 rest with
        | .done checkSum suffix => .done {
            win32VersionValue, sizeOfImage, sizeOfHeaders, checkSum } suffix
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse the image-field block with exact whole-block deficit reporting. -/
def readOptionalHeaderImageFields (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderImageFields :=
  if 16 ≤ input.length then
    readCompleteOptionalHeaderImageFields input
  else
    .needMore (some (16 - input.length))

/-- A truncated image-field block reports its exact missing-byte count. -/
theorem readOptionalHeaderImageFields_short
    {input : Std.Logical.ByteArray} (short : input.length < 16) :
    readOptionalHeaderImageFields input =
      .needMore (some (16 - input.length)) := by
  simp [readOptionalHeaderImageFields, Nat.not_le.mpr short]

/-- Serialize all four image quantities in PE field order. -/
def writeOptionalHeaderImageFields (fields : OptionalHeaderImageFields) :
    Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) fields.win32VersionValue ++
  writeLittleEndian (count := 4) fields.sizeOfImage ++
  writeLittleEndian (count := 4) fields.sizeOfHeaders ++
  writeLittleEndian (count := 4) fields.checkSum

/-- The optional-header image-field block occupies exactly 16 bytes. -/
@[simp] theorem length_writeOptionalHeaderImageFields
    (fields : OptionalHeaderImageFields) :
    (writeOptionalHeaderImageFields fields).length = 16 := by
  simp [writeOptionalHeaderImageFields, writeLittleEndian, isoWriter,
    writeExact]

/-- Every serialized image-field block derives from its typed grammar. -/
theorem writeOptionalHeaderImageFields_derives
    (fields : OptionalHeaderImageFields) :
    Derives optionalHeaderImageFieldsFormat
      (writeOptionalHeaderImageFields fields) fields Vec.empty := by
  rcases fields with ⟨reserved, imageSize, headerSize, checksum⟩
  unfold optionalHeaderImageFieldsFormat
  refine @Derives.iso OptionalHeaderImageFieldProduct OptionalHeaderImageFields
    optionalHeaderImageFieldProductFormat optionalHeaderImageFieldIsomorphism
    _ Vec.empty (reserved, imageSize, headerSize, checksum) ?_
  simp only [writeOptionalHeaderImageFields, Vec.append_assoc]
  unfold optionalHeaderImageFieldProductFormat
  exact Derives.seqAppend ((writeLittleEndian_realizes 4).sound reserved)
    (Derives.seqAppend ((writeLittleEndian_realizes 4).sound imageSize)
      (Derives.seqAppend ((writeLittleEndian_realizes 4).sound headerSize)
        ((writeLittleEndian_realizes 4).sound checksum)))

/-- `readOptionalHeaderImageFields_write_append` states that a serialized
image-field block round-trips while preserving an arbitrary suffix. -/
@[simp] theorem readOptionalHeaderImageFields_write_append
    (fields : OptionalHeaderImageFields) (rest : Std.Logical.ByteArray) :
    readOptionalHeaderImageFields
      (writeOptionalHeaderImageFields fields ++ rest) = .done fields rest := by
  rcases fields with ⟨reserved, imageSize, headerSize, checksum⟩
  simp only [readOptionalHeaderImageFields, Vec.length_append,
    length_writeOptionalHeaderImageFields]
  have enough : 16 ≤ 16 + rest.length := by omega
  simp only [enough, ite_true, readCompleteOptionalHeaderImageFields,
    writeOptionalHeaderImageFields, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]

/-- Whole-input image-field block round trip. -/
@[simp] theorem readOptionalHeaderImageFields_write
    (fields : OptionalHeaderImageFields) :
    readOptionalHeaderImageFields (writeOptionalHeaderImageFields fields) =
      .done fields Vec.empty := by
  simpa using readOptionalHeaderImageFields_write_append fields Vec.empty

end Grass.Artifact.PE
