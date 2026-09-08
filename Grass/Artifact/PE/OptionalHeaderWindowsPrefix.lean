import Grass.Artifact.PE.OptionalHeaderStandard

/-!
# PE32+ Windows-field prefix

The Windows-specific portion of a PE32+ optional header begins with the image
base and its section and file alignments. This module gives that 16-byte block
a typed grammar and concrete reader/writer laws; contextual alignment and
loader constraints remain validation obligations.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Raw PE32+ image-base and alignment fields. -/
structure OptionalHeaderWindowsPrefix where
  imageBase : BitVec 64
  sectionAlignment : BitVec 32
  fileAlignment : BitVec 32
deriving DecidableEq, Repr

/-- Product shape consumed by the generic sequencing grammar. -/
abbrev OptionalHeaderWindowsPrefixProduct :=
  BitVec 64 × BitVec 32 × BitVec 32

/-- Forget field labels while retaining the PE field order. -/
def OptionalHeaderWindowsPrefix.toProduct
    (fields : OptionalHeaderWindowsPrefix) :
    OptionalHeaderWindowsPrefixProduct :=
  (fields.imageBase, fields.sectionAlignment, fields.fileAlignment)

/-- Restore named fields from their grammar product. -/
def OptionalHeaderWindowsPrefix.ofProduct
    (fields : OptionalHeaderWindowsPrefixProduct) :
    OptionalHeaderWindowsPrefix :=
  ⟨fields.1, fields.2.1, fields.2.2⟩

/-- Named prefix fields and their grammar products are totally isomorphic. -/
def optionalHeaderWindowsPrefixIsomorphism :
    Isomorphism OptionalHeaderWindowsPrefixProduct
      OptionalHeaderWindowsPrefix where
  forward := OptionalHeaderWindowsPrefix.ofProduct
  backward := OptionalHeaderWindowsPrefix.toProduct
  backward_forward := by
    intro fields
    rcases fields with ⟨imageBase, sectionAlignment, fileAlignment⟩
    rfl
  forward_backward := by
    intro fields
    rcases fields with ⟨imageBase, sectionAlignment, fileAlignment⟩
    rfl

/-- Generic grammar for the image base and two alignment quantities. -/
def optionalHeaderWindowsPrefixProductFormat :
    Format OptionalHeaderWindowsPrefixProduct :=
  .seq littleEndianU64Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  littleEndianU32Format

/-- Typed language of the 16-byte PE32+ Windows-field prefix. -/
def optionalHeaderWindowsPrefixFormat :
    Format OptionalHeaderWindowsPrefix :=
  optionalHeaderWindowsPrefixProductFormat.iso
    optionalHeaderWindowsPrefixIsomorphism

/-- Decode a Windows-field prefix after its full extent is established. -/
private def readCompleteOptionalHeaderWindowsPrefix
    (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderWindowsPrefix :=
  match takeLittleEndian 8 input with
  | .done imageBase rest =>
    match takeLittleEndian 4 rest with
    | .done sectionAlignment rest =>
      match takeLittleEndian 4 rest with
      | .done fileAlignment suffix =>
        .done ⟨imageBase, sectionAlignment, fileAlignment⟩ suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse the Windows-field prefix with exact whole-block deficit reporting. -/
def readOptionalHeaderWindowsPrefix (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderWindowsPrefix :=
  if 16 ≤ input.length then
    readCompleteOptionalHeaderWindowsPrefix input
  else
    .needMore (some (16 - input.length))

/-- A truncated Windows-field prefix reports its exact missing-byte count. -/
theorem readOptionalHeaderWindowsPrefix_short
    {input : Std.Logical.ByteArray} (short : input.length < 16) :
    readOptionalHeaderWindowsPrefix input =
      .needMore (some (16 - input.length)) := by
  simp [readOptionalHeaderWindowsPrefix, Nat.not_le.mpr short]

/-- Serialize the image base and alignment quantities in PE field order. -/
def writeOptionalHeaderWindowsPrefix
    (fields : OptionalHeaderWindowsPrefix) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 8) fields.imageBase ++
  writeLittleEndian (count := 4) fields.sectionAlignment ++
  writeLittleEndian (count := 4) fields.fileAlignment

/-- The Windows-field prefix occupies exactly 16 bytes. -/
@[simp] theorem length_writeOptionalHeaderWindowsPrefix
    (fields : OptionalHeaderWindowsPrefix) :
    (writeOptionalHeaderWindowsPrefix fields).length = 16 := by
  simp [writeOptionalHeaderWindowsPrefix, writeLittleEndian, isoWriter,
    writeExact]

/-- Every serialized prefix derives from its typed field grammar. -/
theorem writeOptionalHeaderWindowsPrefix_derives
    (fields : OptionalHeaderWindowsPrefix) :
    Derives optionalHeaderWindowsPrefixFormat
      (writeOptionalHeaderWindowsPrefix fields) fields Vec.empty := by
  rcases fields with ⟨imageBase, sectionAlignment, fileAlignment⟩
  unfold optionalHeaderWindowsPrefixFormat
  refine @Derives.iso OptionalHeaderWindowsPrefixProduct
    OptionalHeaderWindowsPrefix optionalHeaderWindowsPrefixProductFormat
    optionalHeaderWindowsPrefixIsomorphism _ Vec.empty
    (imageBase, sectionAlignment, fileAlignment) ?_
  simp only [writeOptionalHeaderWindowsPrefix, Vec.append_assoc]
  unfold optionalHeaderWindowsPrefixProductFormat
  exact Derives.seqAppend
    ((writeLittleEndian_realizes 8).sound imageBase)
    (Derives.seqAppend
      ((writeLittleEndian_realizes 4).sound sectionAlignment)
      ((writeLittleEndian_realizes 4).sound fileAlignment))

/-- A serialized prefix round-trips while preserving an arbitrary suffix. -/
@[simp] theorem readOptionalHeaderWindowsPrefix_write_append
    (fields : OptionalHeaderWindowsPrefix)
    (rest : Std.Logical.ByteArray) :
    readOptionalHeaderWindowsPrefix
      (writeOptionalHeaderWindowsPrefix fields ++ rest) =
      .done fields rest := by
  rcases fields with ⟨imageBase, sectionAlignment, fileAlignment⟩
  simp only [readOptionalHeaderWindowsPrefix, Vec.length_append,
    length_writeOptionalHeaderWindowsPrefix]
  have enough : 16 ≤ 16 + rest.length := by omega
  simp only [enough, ite_true, readCompleteOptionalHeaderWindowsPrefix,
    writeOptionalHeaderWindowsPrefix, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]

/-- Whole-input Windows-field prefix round trip. -/
@[simp] theorem readOptionalHeaderWindowsPrefix_write
    (fields : OptionalHeaderWindowsPrefix) :
    readOptionalHeaderWindowsPrefix (writeOptionalHeaderWindowsPrefix fields) =
      .done fields Vec.empty := by
  simpa using readOptionalHeaderWindowsPrefix_write_append fields Vec.empty

end Grass.Artifact.PE
