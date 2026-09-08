import Grass.Artifact.PE.DataDirectory

/-!
# PE32+ optional-header standard fields

This module models the 24-byte PE32+ standard-field prefix. The fixed magic
selects PE32+ syntax; linker versions and layout quantities remain raw binary
facts, without importing instruction or loader-policy knowledge.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- The format discriminator mandated for a PE32+ optional header. -/
def pe32PlusMagic : BitVec 16 := 0x020b

/-- Grammar containing exactly the little-endian PE32+ magic value. -/
def pe32PlusMagicFormat : Format Unit :=
  littleEndianU16Format.lift fun _ => pe32PlusMagic

/-- Parse and validate the two-byte PE32+ magic discriminator. -/
def readPE32PlusMagic (input : Std.Logical.ByteArray) : ParseResult Unit :=
  match takeLittleEndian 2 input with
  | .done candidate rest =>
      if candidate = pe32PlusMagic then .done () rest
      else .invalid (.malformed "PE32+ optional-header magic mismatch")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Emit the unique two-byte PE32+ magic discriminator. -/
def writePE32PlusMagic (_ : Unit) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 2) pe32PlusMagic

/-- A truncated PE32+ magic reports its exact missing-byte count. -/
theorem readPE32PlusMagic_short {input : Std.Logical.ByteArray}
    (short : input.length < 2) :
    readPE32PlusMagic input = .needMore (some (2 - input.length)) := by
  unfold readPE32PlusMagic takeLittleEndian isoParser
  rw [takeExactSized_short short]
  rfl

/-- The canonical magic round-trips while preserving an arbitrary suffix. -/
@[simp] theorem readPE32PlusMagic_writePE32PlusMagic_append
    (rest : Std.Logical.ByteArray) :
    readPE32PlusMagic (writePE32PlusMagic () ++ rest) = .done () rest := by
  rw [readPE32PlusMagic]
  unfold writePE32PlusMagic
  rw [takeLittleEndian_writeLittleEndian_append]
  simp [pe32PlusMagic]

/-- The canonical magic serialization derives from its singleton grammar. -/
theorem writePE32PlusMagic_derives :
    Derives pe32PlusMagicFormat (writePE32PlusMagic ()) () Vec.empty := by
  apply Derives.lift
  exact (writeLittleEndian_realizes 2).sound pe32PlusMagic

/-- Layout-independent fields following the PE32+ magic discriminator. -/
structure OptionalHeaderStandardFields where
  majorLinkerVersion : Byte
  minorLinkerVersion : Byte
  sizeOfCode : BitVec 32
  sizeOfInitializedData : BitVec 32
  sizeOfUninitializedData : BitVec 32
  addressOfEntryPoint : BitVec 32
  baseOfCode : BitVec 32
deriving DecidableEq, Repr

/-- Product shape consumed by the sequencing grammar for standard fields. -/
abbrev OptionalHeaderStandardFieldProduct :=
  Byte × Byte × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- Forget field labels while preserving standard-field order. -/
def OptionalHeaderStandardFields.toProduct
    (fields : OptionalHeaderStandardFields) :
    OptionalHeaderStandardFieldProduct :=
  (fields.majorLinkerVersion, fields.minorLinkerVersion, fields.sizeOfCode,
    fields.sizeOfInitializedData, fields.sizeOfUninitializedData,
    fields.addressOfEntryPoint, fields.baseOfCode)

/-- Restore named standard fields from their grammar product. -/
def OptionalHeaderStandardFields.ofProduct
    (fields : OptionalHeaderStandardFieldProduct) :
    OptionalHeaderStandardFields where
  majorLinkerVersion := fields.1
  minorLinkerVersion := fields.2.1
  sizeOfCode := fields.2.2.1
  sizeOfInitializedData := fields.2.2.2.1
  sizeOfUninitializedData := fields.2.2.2.2.1
  addressOfEntryPoint := fields.2.2.2.2.2.1
  baseOfCode := fields.2.2.2.2.2.2

/-- Named standard fields and their grammar products are totally isomorphic. -/
def optionalHeaderStandardFieldIsomorphism :
    Isomorphism OptionalHeaderStandardFieldProduct
      OptionalHeaderStandardFields where
  forward := OptionalHeaderStandardFields.ofProduct
  backward := OptionalHeaderStandardFields.toProduct
  backward_forward := by
    intro fields
    rcases fields with ⟨a, b, c, d, e, f, g⟩
    rfl
  forward_backward := by
    intro fields
    rcases fields with ⟨a, b, c, d, e, f, g⟩
    rfl

/-- Sequencing grammar for the 22 bytes following the PE32+ magic. -/
def optionalHeaderStandardFieldProductFormat :
    Format OptionalHeaderStandardFieldProduct :=
  .seq anyByteFormat fun _ =>
  .seq anyByteFormat fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  littleEndianU32Format

/-- Typed language of the 22 layout-independent standard fields. -/
def optionalHeaderStandardFieldsFormat :
    Format OptionalHeaderStandardFields :=
  optionalHeaderStandardFieldProductFormat.iso
    optionalHeaderStandardFieldIsomorphism

/-- Decode the standard fields after their 22-byte extent is established. -/
private def readCompleteOptionalHeaderStandardFields
    (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderStandardFields :=
  match takeByte input with
  | .done majorLinkerVersion rest =>
    match takeByte rest with
    | .done minorLinkerVersion rest =>
      match takeLittleEndian 4 rest with
      | .done sizeOfCode rest =>
        match takeLittleEndian 4 rest with
        | .done sizeOfInitializedData rest =>
          match takeLittleEndian 4 rest with
          | .done sizeOfUninitializedData rest =>
            match takeLittleEndian 4 rest with
            | .done addressOfEntryPoint rest =>
              match takeLittleEndian 4 rest with
              | .done baseOfCode suffix => .done {
                  majorLinkerVersion, minorLinkerVersion, sizeOfCode,
                  sizeOfInitializedData, sizeOfUninitializedData,
                  addressOfEntryPoint, baseOfCode } suffix
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

/-- Parse the 22 fields after the discriminator with exact deficit reporting. -/
def readOptionalHeaderStandardFields (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderStandardFields :=
  if 22 ≤ input.length then
    readCompleteOptionalHeaderStandardFields input
  else
    .needMore (some (22 - input.length))

/-- A short standard-field body reports its exact whole-body deficit. -/
theorem readOptionalHeaderStandardFields_short
    {input : Std.Logical.ByteArray} (short : input.length < 22) :
    readOptionalHeaderStandardFields input =
      .needMore (some (22 - input.length)) := by
  simp [readOptionalHeaderStandardFields, Nat.not_le.mpr short]

/-- Serialize the 22 standard fields following the PE32+ discriminator. -/
def writeOptionalHeaderStandardFields
    (fields : OptionalHeaderStandardFields) : Std.Logical.ByteArray :=
  writeByte fields.majorLinkerVersion ++
  writeByte fields.minorLinkerVersion ++
  writeLittleEndian (count := 4) fields.sizeOfCode ++
  writeLittleEndian (count := 4) fields.sizeOfInitializedData ++
  writeLittleEndian (count := 4) fields.sizeOfUninitializedData ++
  writeLittleEndian (count := 4) fields.addressOfEntryPoint ++
  writeLittleEndian (count := 4) fields.baseOfCode

/-- The standard-field body occupies exactly 22 bytes. -/
@[simp] theorem length_writeOptionalHeaderStandardFields
    (fields : OptionalHeaderStandardFields) :
    (writeOptionalHeaderStandardFields fields).length = 22 := by
  simp [writeOptionalHeaderStandardFields, writeByte, writeLittleEndian,
    isoWriter, writeExact]

/-- Every standard-field body derives from its typed sequencing grammar. -/
theorem writeOptionalHeaderStandardFields_derives
    (fields : OptionalHeaderStandardFields) :
    Derives optionalHeaderStandardFieldsFormat
      (writeOptionalHeaderStandardFields fields) fields Vec.empty := by
  rcases fields with ⟨major, minor, code, initialized, uninitialized,
    entry, base⟩
  unfold optionalHeaderStandardFieldsFormat
  refine @Derives.iso OptionalHeaderStandardFieldProduct
    OptionalHeaderStandardFields optionalHeaderStandardFieldProductFormat
    optionalHeaderStandardFieldIsomorphism _ Vec.empty
    (major, minor, code, initialized, uninitialized, entry, base) ?_
  simp only [writeOptionalHeaderStandardFields, Vec.append_assoc]
  unfold optionalHeaderStandardFieldProductFormat
  exact Derives.seqAppend (writeByte_realizes.sound major)
    (Derives.seqAppend (writeByte_realizes.sound minor)
      (Derives.seqAppend ((writeLittleEndian_realizes 4).sound code)
        (Derives.seqAppend
          ((writeLittleEndian_realizes 4).sound initialized)
          (Derives.seqAppend
            ((writeLittleEndian_realizes 4).sound uninitialized)
            (Derives.seqAppend
              ((writeLittleEndian_realizes 4).sound entry)
              ((writeLittleEndian_realizes 4).sound base))))))

/-- The standard-field body round-trips with exact suffix preservation. -/
@[simp] theorem readOptionalHeaderStandardFields_write_append
    (fields : OptionalHeaderStandardFields)
    (rest : Std.Logical.ByteArray) :
    readOptionalHeaderStandardFields
      (writeOptionalHeaderStandardFields fields ++ rest) =
      .done fields rest := by
  rcases fields with ⟨major, minor, code, initialized, uninitialized,
    entry, base⟩
  simp only [readOptionalHeaderStandardFields, Vec.length_append,
    length_writeOptionalHeaderStandardFields]
  have enough : 22 ≤ 22 + rest.length := by omega
  simp only [enough, ite_true, readCompleteOptionalHeaderStandardFields,
    writeOptionalHeaderStandardFields, Vec.append_assoc,
    takeByte_writeByte_append, takeLittleEndian_writeLittleEndian_append]

/-- Complete PE32+ standard fields, with the fixed discriminator implicit. -/
abbrev OptionalHeaderStandard := OptionalHeaderStandardFields

/-- Typed grammar for the complete 24-byte PE32+ standard-field prefix. -/
def optionalHeaderStandardFormat : Format OptionalHeaderStandard :=
  (Format.seq pe32PlusMagicFormat fun _ =>
    optionalHeaderStandardFieldsFormat).lift fun standard => ((), standard)

/-- Parse the complete 24-byte PE32+ standard-field prefix. -/
def readOptionalHeaderStandard (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderStandard :=
  if 24 ≤ input.length then
    match readPE32PlusMagic input with
    | .done _ afterMagic => readOptionalHeaderStandardFields afterMagic
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else
    .needMore (some (24 - input.length))

/-- A short complete standard prefix reports its exact 24-byte deficit. -/
theorem readOptionalHeaderStandard_short {input : Std.Logical.ByteArray}
    (short : input.length < 24) :
    readOptionalHeaderStandard input =
      .needMore (some (24 - input.length)) := by
  simp [readOptionalHeaderStandard, Nat.not_le.mpr short]

/-- Serialize the PE32+ discriminator and its standard fields. -/
def writeOptionalHeaderStandard (standard : OptionalHeaderStandard) :
    Std.Logical.ByteArray :=
  writePE32PlusMagic () ++ writeOptionalHeaderStandardFields standard

/-- A complete PE32+ standard-field prefix occupies exactly 24 bytes. -/
@[simp] theorem length_writeOptionalHeaderStandard
    (standard : OptionalHeaderStandard) :
    (writeOptionalHeaderStandard standard).length = 24 := by
  simp [writeOptionalHeaderStandard, writePE32PlusMagic,
    writeLittleEndian, isoWriter, writeExact]

/-- Complete PE32+ standard fields round-trip and preserve any suffix. -/
@[simp] theorem readOptionalHeaderStandard_write_append
    (standard : OptionalHeaderStandard) (rest : Std.Logical.ByteArray) :
    readOptionalHeaderStandard
      (writeOptionalHeaderStandard standard ++ rest) =
      .done standard rest := by
  simp only [readOptionalHeaderStandard, Vec.length_append,
    length_writeOptionalHeaderStandard]
  have enough : 24 ≤ 24 + rest.length := by omega
  simp only [enough, ite_true, writeOptionalHeaderStandard,
    Vec.append_assoc, readPE32PlusMagic_writePE32PlusMagic_append,
    readOptionalHeaderStandardFields_write_append]

/-- Every complete standard prefix derives from its PE32+ grammar. -/
theorem writeOptionalHeaderStandard_derives
    (standard : OptionalHeaderStandard) :
    Derives optionalHeaderStandardFormat
      (writeOptionalHeaderStandard standard) standard Vec.empty := by
  unfold optionalHeaderStandardFormat
  apply Derives.lift
  exact Derives.seqAppend writePE32PlusMagic_derives
    (writeOptionalHeaderStandardFields_derives standard)

end Grass.Artifact.PE
