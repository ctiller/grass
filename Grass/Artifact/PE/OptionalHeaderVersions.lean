import Grass.Artifact.PE.OptionalHeaderWindowsPrefix

/-!
# PE32+ optional-header version fields

This module models the six ordered 16-bit version quantities following the
image-base/alignment prefix. They remain raw format values: support policy and
host compatibility are loader-validation concerns.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- The operating-system, image, and subsystem version pairs in field order. -/
structure OptionalHeaderVersions where
  majorOperatingSystemVersion : BitVec 16
  minorOperatingSystemVersion : BitVec 16
  majorImageVersion : BitVec 16
  minorImageVersion : BitVec 16
  majorSubsystemVersion : BitVec 16
  minorSubsystemVersion : BitVec 16
deriving DecidableEq, Repr

/-- Product shape consumed by the generic sequencing grammar. -/
abbrev OptionalHeaderVersionsProduct :=
  BitVec 16 × BitVec 16 × BitVec 16 × BitVec 16 × BitVec 16 × BitVec 16

/-- Forget version-field labels while preserving their binary order. -/
def OptionalHeaderVersions.toProduct (versions : OptionalHeaderVersions) :
    OptionalHeaderVersionsProduct :=
  (versions.majorOperatingSystemVersion,
    versions.minorOperatingSystemVersion,
    versions.majorImageVersion,
    versions.minorImageVersion,
    versions.majorSubsystemVersion,
    versions.minorSubsystemVersion)

/-- Restore named version fields from their grammar product. -/
def OptionalHeaderVersions.ofProduct
    (versions : OptionalHeaderVersionsProduct) : OptionalHeaderVersions where
  majorOperatingSystemVersion := versions.1
  minorOperatingSystemVersion := versions.2.1
  majorImageVersion := versions.2.2.1
  minorImageVersion := versions.2.2.2.1
  majorSubsystemVersion := versions.2.2.2.2.1
  minorSubsystemVersion := versions.2.2.2.2.2

/-- Named version fields and their grammar products are totally isomorphic. -/
def optionalHeaderVersionsIsomorphism :
    Isomorphism OptionalHeaderVersionsProduct OptionalHeaderVersions where
  forward := OptionalHeaderVersions.ofProduct
  backward := OptionalHeaderVersions.toProduct
  backward_forward := by
    intro versions
    rcases versions with ⟨a, b, c, d, e, f⟩
    rfl
  forward_backward := by
    intro versions
    rcases versions with ⟨a, b, c, d, e, f⟩
    rfl

/-- Generic grammar for the six little-endian 16-bit version fields. -/
def optionalHeaderVersionsProductFormat :
    Format OptionalHeaderVersionsProduct :=
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  littleEndianU16Format

/-- Typed language of the 12-byte optional-header version block. -/
def optionalHeaderVersionsFormat : Format OptionalHeaderVersions :=
  optionalHeaderVersionsProductFormat.iso optionalHeaderVersionsIsomorphism

/-- Decode version fields after establishing the complete 12-byte extent. -/
private def readCompleteOptionalHeaderVersions
    (input : Std.Logical.ByteArray) : ParseResult OptionalHeaderVersions :=
  match takeLittleEndian 2 input with
  | .done majorOperatingSystemVersion rest =>
    match takeLittleEndian 2 rest with
    | .done minorOperatingSystemVersion rest =>
      match takeLittleEndian 2 rest with
      | .done majorImageVersion rest =>
        match takeLittleEndian 2 rest with
        | .done minorImageVersion rest =>
          match takeLittleEndian 2 rest with
          | .done majorSubsystemVersion rest =>
            match takeLittleEndian 2 rest with
            | .done minorSubsystemVersion suffix => .done {
                majorOperatingSystemVersion, minorOperatingSystemVersion,
                majorImageVersion, minorImageVersion,
                majorSubsystemVersion, minorSubsystemVersion } suffix
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

/-- Parse the version block with exact whole-block deficit reporting. -/
def readOptionalHeaderVersions (input : Std.Logical.ByteArray) :
    ParseResult OptionalHeaderVersions :=
  if 12 ≤ input.length then
    readCompleteOptionalHeaderVersions input
  else
    .needMore (some (12 - input.length))

/-- A truncated version block reports its exact missing-byte count. -/
theorem readOptionalHeaderVersions_short {input : Std.Logical.ByteArray}
    (short : input.length < 12) :
    readOptionalHeaderVersions input =
      .needMore (some (12 - input.length)) := by
  simp [readOptionalHeaderVersions, Nat.not_le.mpr short]

/-- Serialize all six version quantities in PE field order. -/
def writeOptionalHeaderVersions (versions : OptionalHeaderVersions) :
    Std.Logical.ByteArray :=
  writeLittleEndian (count := 2) versions.majorOperatingSystemVersion ++
  writeLittleEndian (count := 2) versions.minorOperatingSystemVersion ++
  writeLittleEndian (count := 2) versions.majorImageVersion ++
  writeLittleEndian (count := 2) versions.minorImageVersion ++
  writeLittleEndian (count := 2) versions.majorSubsystemVersion ++
  writeLittleEndian (count := 2) versions.minorSubsystemVersion

/-- The optional-header version block occupies exactly 12 bytes. -/
@[simp] theorem length_writeOptionalHeaderVersions
    (versions : OptionalHeaderVersions) :
    (writeOptionalHeaderVersions versions).length = 12 := by
  simp [writeOptionalHeaderVersions, writeLittleEndian, isoWriter, writeExact]

/-- Every serialized version block derives from its typed grammar. -/
theorem writeOptionalHeaderVersions_derives
    (versions : OptionalHeaderVersions) :
    Derives optionalHeaderVersionsFormat
      (writeOptionalHeaderVersions versions) versions Vec.empty := by
  rcases versions with ⟨a, b, c, d, e, f⟩
  unfold optionalHeaderVersionsFormat
  refine @Derives.iso OptionalHeaderVersionsProduct OptionalHeaderVersions
    optionalHeaderVersionsProductFormat optionalHeaderVersionsIsomorphism
    _ Vec.empty (a, b, c, d, e, f) ?_
  simp only [writeOptionalHeaderVersions, Vec.append_assoc]
  unfold optionalHeaderVersionsProductFormat
  exact Derives.seqAppend ((writeLittleEndian_realizes 2).sound a)
    (Derives.seqAppend ((writeLittleEndian_realizes 2).sound b)
      (Derives.seqAppend ((writeLittleEndian_realizes 2).sound c)
        (Derives.seqAppend ((writeLittleEndian_realizes 2).sound d)
          (Derives.seqAppend ((writeLittleEndian_realizes 2).sound e)
            ((writeLittleEndian_realizes 2).sound f)))))

/-- `readOptionalHeaderVersions_write_append` states that a serialized version
block round-trips and preserves any suffix. -/
@[simp] theorem readOptionalHeaderVersions_write_append
    (versions : OptionalHeaderVersions) (rest : Std.Logical.ByteArray) :
    readOptionalHeaderVersions (writeOptionalHeaderVersions versions ++ rest) =
      .done versions rest := by
  rcases versions with ⟨a, b, c, d, e, f⟩
  simp only [readOptionalHeaderVersions, Vec.length_append,
    length_writeOptionalHeaderVersions]
  have enough : 12 ≤ 12 + rest.length := by omega
  simp only [enough, ite_true, readCompleteOptionalHeaderVersions,
    writeOptionalHeaderVersions, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]

/-- Whole-input version-block round trip. -/
@[simp] theorem readOptionalHeaderVersions_write
    (versions : OptionalHeaderVersions) :
    readOptionalHeaderVersions (writeOptionalHeaderVersions versions) =
      .done versions Vec.empty := by
  simpa using readOptionalHeaderVersions_write_append versions Vec.empty

end Grass.Artifact.PE
