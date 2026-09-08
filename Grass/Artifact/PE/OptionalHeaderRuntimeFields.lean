import Grass.Artifact.PE.OptionalHeaderImageFields

/-!
# PE32+ optional-header runtime fields

This module models the final 44 bytes before the data-directory table:
subsystem and DLL flags, stack and heap size pairs, loader flags, and the
declared directory count. Bit meanings and cross-field constraints remain
separate validation facts.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Raw runtime-facing fields at the end of the fixed PE32+ optional header. -/
structure OptionalHeaderRuntimeFields where
  subsystem : BitVec 16
  dllCharacteristics : BitVec 16
  sizeOfStackReserve : BitVec 64
  sizeOfStackCommit : BitVec 64
  sizeOfHeapReserve : BitVec 64
  sizeOfHeapCommit : BitVec 64
  loaderFlags : BitVec 32
  numberOfRvaAndSizes : BitVec 32
deriving DecidableEq, Repr

/-- Product shape consumed by the generic sequencing grammar. -/
abbrev OptionalHeaderRuntimeFieldProduct :=
  BitVec 16 × BitVec 16 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 32 × BitVec 32

/-- Forget field labels while preserving PE binary order. -/
def OptionalHeaderRuntimeFields.toProduct
    (fields : OptionalHeaderRuntimeFields) :
    OptionalHeaderRuntimeFieldProduct :=
  (fields.subsystem, fields.dllCharacteristics,
    fields.sizeOfStackReserve, fields.sizeOfStackCommit,
    fields.sizeOfHeapReserve, fields.sizeOfHeapCommit,
    fields.loaderFlags, fields.numberOfRvaAndSizes)

/-- Restore named runtime fields from their grammar product. -/
def OptionalHeaderRuntimeFields.ofProduct
    (fields : OptionalHeaderRuntimeFieldProduct) :
    OptionalHeaderRuntimeFields where
  subsystem := fields.1
  dllCharacteristics := fields.2.1
  sizeOfStackReserve := fields.2.2.1
  sizeOfStackCommit := fields.2.2.2.1
  sizeOfHeapReserve := fields.2.2.2.2.1
  sizeOfHeapCommit := fields.2.2.2.2.2.1
  loaderFlags := fields.2.2.2.2.2.2.1
  numberOfRvaAndSizes := fields.2.2.2.2.2.2.2

/-- Named runtime fields and their grammar products are totally isomorphic. -/
def optionalHeaderRuntimeFieldIsomorphism :
    Isomorphism OptionalHeaderRuntimeFieldProduct
      OptionalHeaderRuntimeFields where
  forward := OptionalHeaderRuntimeFields.ofProduct
  backward := OptionalHeaderRuntimeFields.toProduct
  backward_forward := by
    intro fields
    rcases fields with ⟨a, b, c, d, e, f, g, h⟩
    rfl
  forward_backward := by
    intro fields
    rcases fields with ⟨a, b, c, d, e, f, g, h⟩
    rfl

/-- Generic grammar for the eight runtime-facing fields. -/
def optionalHeaderRuntimeFieldProductFormat :
    Format OptionalHeaderRuntimeFieldProduct :=
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU64Format fun _ =>
  .seq littleEndianU64Format fun _ =>
  .seq littleEndianU64Format fun _ =>
  .seq littleEndianU64Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  littleEndianU32Format

/-- Typed language of the 44-byte optional-header runtime-field block. -/
def optionalHeaderRuntimeFieldsFormat :
    Format OptionalHeaderRuntimeFields :=
  optionalHeaderRuntimeFieldProductFormat.iso
    optionalHeaderRuntimeFieldIsomorphism

/-- Decode runtime fields after establishing their complete 44-byte extent. -/
private def readCompleteOptionalHeaderRuntimeFields
    (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderRuntimeFields :=
  match takeLittleEndian 2 input with
  | .done subsystem rest =>
    match takeLittleEndian 2 rest with
    | .done dllCharacteristics rest =>
      match takeLittleEndian 8 rest with
      | .done sizeOfStackReserve rest =>
        match takeLittleEndian 8 rest with
        | .done sizeOfStackCommit rest =>
          match takeLittleEndian 8 rest with
          | .done sizeOfHeapReserve rest =>
            match takeLittleEndian 8 rest with
            | .done sizeOfHeapCommit rest =>
              match takeLittleEndian 4 rest with
              | .done loaderFlags rest =>
                match takeLittleEndian 4 rest with
                | .done numberOfRvaAndSizes suffix => .done {
                    subsystem, dllCharacteristics,
                    sizeOfStackReserve, sizeOfStackCommit,
                    sizeOfHeapReserve, sizeOfHeapCommit,
                    loaderFlags, numberOfRvaAndSizes } suffix
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

/-- Parse the runtime-field block with exact whole-block deficit reporting. -/
def readOptionalHeaderRuntimeFields (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderRuntimeFields :=
  if 44 ≤ input.length then
    readCompleteOptionalHeaderRuntimeFields input
  else
    .needMore (some (44 - input.length))

/-- A truncated runtime-field block reports its exact missing-byte count. -/
theorem readOptionalHeaderRuntimeFields_short
    {input : Std.Logical.ByteArray} (short : input.length < 44) :
    readOptionalHeaderRuntimeFields input =
      .needMore (some (44 - input.length)) := by
  simp [readOptionalHeaderRuntimeFields, Nat.not_le.mpr short]

/-- Serialize all eight runtime-facing quantities in PE field order. -/
def writeOptionalHeaderRuntimeFields
    (fields : OptionalHeaderRuntimeFields) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 2) fields.subsystem ++
  writeLittleEndian (count := 2) fields.dllCharacteristics ++
  writeLittleEndian (count := 8) fields.sizeOfStackReserve ++
  writeLittleEndian (count := 8) fields.sizeOfStackCommit ++
  writeLittleEndian (count := 8) fields.sizeOfHeapReserve ++
  writeLittleEndian (count := 8) fields.sizeOfHeapCommit ++
  writeLittleEndian (count := 4) fields.loaderFlags ++
  writeLittleEndian (count := 4) fields.numberOfRvaAndSizes

/-- The optional-header runtime-field block occupies exactly 44 bytes. -/
@[simp] theorem length_writeOptionalHeaderRuntimeFields
    (fields : OptionalHeaderRuntimeFields) :
    (writeOptionalHeaderRuntimeFields fields).length = 44 := by
  simp [writeOptionalHeaderRuntimeFields, writeLittleEndian, isoWriter,
    writeExact]

/-- Every serialized runtime-field block derives from its typed grammar. -/
theorem writeOptionalHeaderRuntimeFields_derives
    (fields : OptionalHeaderRuntimeFields) :
    Derives optionalHeaderRuntimeFieldsFormat
      (writeOptionalHeaderRuntimeFields fields) fields Vec.empty := by
  rcases fields with ⟨a, b, c, d, e, f, g, h⟩
  unfold optionalHeaderRuntimeFieldsFormat
  refine @Derives.iso OptionalHeaderRuntimeFieldProduct
    OptionalHeaderRuntimeFields optionalHeaderRuntimeFieldProductFormat
    optionalHeaderRuntimeFieldIsomorphism _ Vec.empty
    (a, b, c, d, e, f, g, h) ?_
  simp only [writeOptionalHeaderRuntimeFields, Vec.append_assoc]
  unfold optionalHeaderRuntimeFieldProductFormat
  exact Derives.seqAppend ((writeLittleEndian_realizes 2).sound a)
    (Derives.seqAppend ((writeLittleEndian_realizes 2).sound b)
      (Derives.seqAppend ((writeLittleEndian_realizes 8).sound c)
        (Derives.seqAppend ((writeLittleEndian_realizes 8).sound d)
          (Derives.seqAppend ((writeLittleEndian_realizes 8).sound e)
            (Derives.seqAppend ((writeLittleEndian_realizes 8).sound f)
              (Derives.seqAppend ((writeLittleEndian_realizes 4).sound g)
                ((writeLittleEndian_realizes 4).sound h)))))))

/-- `readOptionalHeaderRuntimeFields_write_append` states that serialized
runtime fields round-trip while preserving an arbitrary suffix. -/
@[simp] theorem readOptionalHeaderRuntimeFields_write_append
    (fields : OptionalHeaderRuntimeFields) (rest : Std.Logical.ByteArray) :
    readOptionalHeaderRuntimeFields
      (writeOptionalHeaderRuntimeFields fields ++ rest) = .done fields rest := by
  rcases fields with ⟨a, b, c, d, e, f, g, h⟩
  simp only [readOptionalHeaderRuntimeFields, Vec.length_append,
    length_writeOptionalHeaderRuntimeFields]
  have enough : 44 ≤ 44 + rest.length := by omega
  simp only [enough, ite_true, readCompleteOptionalHeaderRuntimeFields,
    writeOptionalHeaderRuntimeFields, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]

/-- Whole-input runtime-field block round trip. -/
@[simp] theorem readOptionalHeaderRuntimeFields_write
    (fields : OptionalHeaderRuntimeFields) :
    readOptionalHeaderRuntimeFields (writeOptionalHeaderRuntimeFields fields) =
      .done fields Vec.empty := by
  simpa using readOptionalHeaderRuntimeFields_write_append fields Vec.empty

end Grass.Artifact.PE
