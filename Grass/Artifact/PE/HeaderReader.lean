import Grass.Artifact.PE.HeaderPrefix

/-!
# Canonical PE32+ prefix reader

`takeHeaderPrefix` recognizes exactly the canonical prefix emitted by
`writeHeaderPrefix`, returns the COFF section count, and preserves the complete
unconsumed suffix. Short input is repairable by its exact deficit; a complete
noncanonical prefix is malformed.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical Grass.Grammar Grass.Artifact.Binary

/-- Width of the canonical DOS, signature, and COFF prefix. -/
def headerPrefixSize : Nat := canonicalPeOffset + peSignatureSize + coffHeaderSize

/-- The two section-count bytes inside an already isolated canonical-width
prefix. -/
def headerSectionCountBytes (headerBytes : Std.Logical.ByteArray) :
    Std.Logical.ByteArray :=
  (headerBytes.drop 70).take 2

/-- The writer puts the little-endian section count immediately after the
seventy-byte fixed leading region. -/
@[simp] theorem headerSectionCountBytes_writeHeaderPrefix (sectionCount : BitVec 16) :
    headerSectionCountBytes (writeHeaderPrefix sectionCount) =
      writeLittleEndian (count := 2) sectionCount := by
  unfold headerSectionCountBytes writeHeaderPrefix
  rw [Vec.append_assoc]
  rw [Vec.drop_append_of_length_eq length_writeHeaderPrefixLeading]
  have countLength :
      (writeLittleEndian (count := 2) sectionCount).length = 2 :=
    @length_writeLittleEndian 2 sectionCount
  exact Vec.take_append_of_length_eq
    (u := writeLittleEndian (count := 2) sectionCount) (n := 2)
    countLength writeHeaderPrefixTrailing

/-- Decide whether a short byte sequence is the prefix of some canonical
header. The two section-count bytes are unconstrained; bytes before and after
them must agree with the fixed writer regions. -/
def headerPrefixCompatible (input : Std.Logical.ByteArray) : Bool :=
  if input.length ≤ 70 then
    decide (input = writeHeaderPrefixLeading.take input.length)
  else if input.length ≤ 72 then
    decide (input.take 70 = writeHeaderPrefixLeading)
  else
    decide (input.take 70 = writeHeaderPrefixLeading) &&
      decide (input.drop 72 = writeHeaderPrefixTrailing.take (input.length - 72))

/-- Read the canonical prefix and recover its section count. -/
def takeHeaderPrefix (input : Std.Logical.ByteArray) : ParseResult (BitVec 16) :=
  if _enough : headerPrefixSize ≤ input.length then
    let headerBytes := input.take headerPrefixSize
    let countBytes := headerSectionCountBytes headerBytes
    match takeLittleEndian 2 countBytes with
    | .done sectionCount _ =>
        if headerBytes = writeHeaderPrefix sectionCount then
          .done sectionCount (input.drop headerPrefixSize)
        else .invalid (.malformed "noncanonical PE header prefix")
    | _ => .invalid (.malformed "unreadable PE section count")
  else if headerPrefixCompatible input then
    .needMore (some (headerPrefixSize - input.length))
  else .invalid (.malformed "impossible PE header prefix")

/-- A canonical written prefix is read exactly and leaves an arbitrary suffix
untouched. -/
@[simp] theorem takeHeaderPrefix_writeHeaderPrefix_append
    (sectionCount : BitVec 16) (rest : Std.Logical.ByteArray) :
    takeHeaderPrefix (writeHeaderPrefix sectionCount ++ rest) =
      .done sectionCount rest := by
  unfold takeHeaderPrefix
  have prefixLength : (writeHeaderPrefix sectionCount).length = headerPrefixSize := by
    simp [headerPrefixSize]
  simp only [Vec.length_append, prefixLength]
  rw [dif_pos (Nat.le_add_right _ _)]
  rw [Vec.take_append_of_length_eq prefixLength]
  rw [Vec.drop_append_of_length_eq prefixLength]
  rw [headerSectionCountBytes_writeHeaderPrefix]
  rw [takeLittleEndian_writeLittleEndian]
  simp

/-- Complete-input canonical prefix round trip. -/
@[simp] theorem takeHeaderPrefix_writeHeaderPrefix (sectionCount : BitVec 16) :
    takeHeaderPrefix (writeHeaderPrefix sectionCount) =
      .done sectionCount Vec.empty := by
  simpa using takeHeaderPrefix_writeHeaderPrefix_append sectionCount Vec.empty

end Grass.Artifact.PE
