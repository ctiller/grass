import Grass.Artifact.PE.OptionalHeaderRuntimeFields

/-!
# Canonical PE32+ optional header

The canonical optional header composes the 112 fixed PE32+ bytes with the
sixteen-entry data-directory table. Its value type couples the declared
directory count to that table; loader legality and cross-field layout policy
remain later validation layers.
-/

namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical

/-- A complete canonical PE32+ optional header with its directory-count proof. -/
structure OptionalHeader where
  standard : OptionalHeaderStandard
  windowsPrefix : OptionalHeaderWindowsPrefix
  versions : OptionalHeaderVersions
  imageFields : OptionalHeaderImageFields
  runtimeFields : OptionalHeaderRuntimeFields
  directories : DataDirectoryTable
  directoryCount : runtimeFields.numberOfRvaAndSizes.toNat = 16
deriving DecidableEq, Repr

/-- Product shape generated directly by sequencing the component grammars. -/
abbrev OptionalHeaderProduct :=
  OptionalHeaderStandard × OptionalHeaderWindowsPrefix ×
    OptionalHeaderVersions × OptionalHeaderImageFields ×
    OptionalHeaderRuntimeFields × DataDirectoryTable

/-- Grammar product refined by the canonical sixteen-directory declaration. -/
abbrev CheckedOptionalHeader :=
  {fields : OptionalHeaderProduct //
    fields.2.2.2.2.1.numberOfRvaAndSizes.toNat = 16}

/-- Restore a named optional header from its count-checked grammar product. -/
def OptionalHeader.ofChecked (fields : CheckedOptionalHeader) :
    OptionalHeader where
  standard := fields.1.1
  windowsPrefix := fields.1.2.1
  versions := fields.1.2.2.1
  imageFields := fields.1.2.2.2.1
  runtimeFields := fields.1.2.2.2.2.1
  directories := fields.1.2.2.2.2.2
  directoryCount := fields.2

/-- Forget field labels while retaining the exact directory-count proof. -/
def OptionalHeader.toChecked (header : OptionalHeader) :
    CheckedOptionalHeader :=
  ⟨(header.standard, header.windowsPrefix, header.versions,
    header.imageFields, header.runtimeFields, header.directories),
    header.directoryCount⟩

/-- Named optional headers and checked grammar products are totally isomorphic. -/
def optionalHeaderIsomorphism :
    Isomorphism CheckedOptionalHeader OptionalHeader where
  forward := OptionalHeader.ofChecked
  backward := OptionalHeader.toChecked
  backward_forward := by
    intro fields
    rcases fields with ⟨⟨a, b, c, d, e, f⟩, count⟩
    rfl
  forward_backward := by
    intro header
    rcases header with ⟨a, b, c, d, e, f, count⟩
    rfl

/-- Unrefined sequencing grammar for all six optional-header components. -/
def rawOptionalHeaderFormat : Format OptionalHeaderProduct :=
  .seq optionalHeaderStandardFormat fun _ =>
  .seq optionalHeaderWindowsPrefixFormat fun _ =>
  .seq optionalHeaderVersionsFormat fun _ =>
  .seq optionalHeaderImageFieldsFormat fun _ =>
  .seq optionalHeaderRuntimeFieldsFormat fun _ =>
  dataDirectoryTableFormat

/-- Promote the declared sixteen-directory invariant into the grammar value. -/
def checkedOptionalHeaderFormat : Format CheckedOptionalHeader :=
  rawOptionalHeaderFormat.refineValue fun fields =>
    fields.2.2.2.2.1.numberOfRvaAndSizes.toNat = 16

/-- Typed grammar of a complete canonical PE32+ optional header. -/
def optionalHeaderFormat : Format OptionalHeader :=
  checkedOptionalHeaderFormat.iso optionalHeaderIsomorphism

/-- Parse all 240 bytes and reject a noncanonical directory declaration. -/
def readOptionalHeader (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeader :=
  if 240 ≤ input.length then
    match readOptionalHeaderStandard input with
    | .done standard afterStandard =>
      match readOptionalHeaderWindowsPrefix afterStandard with
      | .done windowsPrefix afterWindowsPrefix =>
        match readOptionalHeaderVersions afterWindowsPrefix with
        | .done versions afterVersions =>
          match readOptionalHeaderImageFields afterVersions with
          | .done imageFields afterImageFields =>
            match readOptionalHeaderRuntimeFields afterImageFields with
            | .done runtimeFields afterRuntimeFields =>
              match readDataDirectoryTable afterRuntimeFields with
              | .done directories rest =>
                if count : runtimeFields.numberOfRvaAndSizes.toNat = 16 then
                  .done {
                    standard, windowsPrefix, versions, imageFields,
                    runtimeFields, directories, directoryCount := count } rest
                else
                  .invalid (.malformed
                    "PE32+ canonical data-directory count mismatch")
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
  else
    .needMore (some (240 - input.length))

/-- A truncated optional header reports its exact whole-header byte deficit. -/
theorem readOptionalHeader_short {input : Std.Logical.ByteArray}
    (short : input.length < 240) :
    readOptionalHeader input =
      .needMore (some (240 - input.length)) := by
  simp [readOptionalHeader, Nat.not_le.mpr short]

/-- Serialize all fixed fields and the canonical data-directory table. -/
def writeOptionalHeader (header : OptionalHeader) : Std.Logical.ByteArray :=
  writeOptionalHeaderStandard header.standard ++
  writeOptionalHeaderWindowsPrefix header.windowsPrefix ++
  writeOptionalHeaderVersions header.versions ++
  writeOptionalHeaderImageFields header.imageFields ++
  writeOptionalHeaderRuntimeFields header.runtimeFields ++
  writeDataDirectoryTable header.directories

/-- A canonical PE32+ optional header occupies exactly 240 bytes. -/
@[simp] theorem length_writeOptionalHeader (header : OptionalHeader) :
    (writeOptionalHeader header).length = 240 := by
  simp [writeOptionalHeader]

/-- `readOptionalHeader_write_append` states that a canonical optional header
round-trips while preserving an arbitrary suffix. -/
@[simp] theorem readOptionalHeader_write_append
    (header : OptionalHeader) (rest : Std.Logical.ByteArray) :
    readOptionalHeader (writeOptionalHeader header ++ rest) =
      .done header rest := by
  rcases header with ⟨standard, windowsPrefix, versions, imageFields,
    runtimeFields, directories, count⟩
  simp only [readOptionalHeader, Vec.length_append, length_writeOptionalHeader]
  have enough : 240 ≤ 240 + rest.length := by omega
  simp only [enough, ite_true, writeOptionalHeader, Vec.append_assoc,
    readOptionalHeaderStandard_write_append,
    readOptionalHeaderWindowsPrefix_write_append,
    readOptionalHeaderVersions_write_append,
    readOptionalHeaderImageFields_write_append,
    readOptionalHeaderRuntimeFields_write_append,
    readDataDirectoryTable_writeDataDirectoryTable_append,
    count, ↓reduceDIte]

/-- Whole-input canonical optional-header round trip. -/
@[simp] theorem readOptionalHeader_write (header : OptionalHeader) :
    readOptionalHeader (writeOptionalHeader header) =
      .done header Vec.empty := by
  simpa using readOptionalHeader_write_append header Vec.empty

/-- Every canonical optional-header serialization derives from its grammar. -/
theorem writeOptionalHeader_derives (header : OptionalHeader) :
    Derives optionalHeaderFormat (writeOptionalHeader header)
      header Vec.empty := by
  rcases header with ⟨standard, windowsPrefix, versions, imageFields,
    runtimeFields, directories, count⟩
  unfold optionalHeaderFormat
  refine @Derives.iso CheckedOptionalHeader OptionalHeader
    checkedOptionalHeaderFormat optionalHeaderIsomorphism _ Vec.empty
    ⟨(standard, windowsPrefix, versions, imageFields,
      runtimeFields, directories), count⟩ ?_
  unfold checkedOptionalHeaderFormat
  apply Derives.lift
  simp only [writeOptionalHeader, Vec.append_assoc]
  unfold rawOptionalHeaderFormat
  exact Derives.seqAppend
    (writeOptionalHeaderStandard_derives standard)
    (Derives.seqAppend
      (writeOptionalHeaderWindowsPrefix_derives windowsPrefix)
      (Derives.seqAppend
        (writeOptionalHeaderVersions_derives versions)
        (Derives.seqAppend
          (writeOptionalHeaderImageFields_derives imageFields)
          (Derives.seqAppend
            (writeOptionalHeaderRuntimeFields_derives runtimeFields)
            (writeDataDirectoryTable_derives directories)))))

end Grass.Artifact.PE
