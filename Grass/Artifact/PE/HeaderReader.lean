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

/-- The typed language of canonical PE image prefixes. A value is the COFF
section count; its byte representation fixes every other DOS, signature, and
COFF field. -/
def headerPrefixFormat : Format (BitVec 16) :=
  .lift (fixedBytesFormat headerPrefixSize) fun sectionCount =>
    ⟨writeHeaderPrefix sectionCount, by simp [headerPrefixSize]⟩

/-- `derives_headerPrefix_iff` states that a canonical header derivation
consumes precisely the writer bytes and preserves precisely the caller's
suffix. -/
theorem derives_headerPrefix_iff {input rest : Std.Logical.ByteArray}
    {sectionCount : BitVec 16} :
    Derives headerPrefixFormat input sectionCount rest ↔
      input = writeHeaderPrefix sectionCount ++ rest := by
  constructor
  · intro derivation
    have fixed := derivation.lift_inner
    have repeated := derives_fixedBytes_iff.mp fixed
    exact (derives_repeatedBytes_iff.mp repeated).1
  · intro equality
    rw [equality]
    apply Derives.lift
    apply derives_fixedBytes_iff.mpr
    simpa [headerPrefixSize] using
      anyBytes_derives (writeHeaderPrefix sectionCount) rest

/-- The canonical writer inhabits the header-prefix format without any
unconsumed bytes. -/
theorem writeHeaderPrefix_derives (sectionCount : BitVec 16) :
    Derives headerPrefixFormat (writeHeaderPrefix sectionCount) sectionCount
      Vec.empty :=
  derives_headerPrefix_iff.mpr (by simp)

/-- Before the section-count field, every canonical header has the same
prefix, independently of the count value. -/
theorem take_writeHeaderPrefix_of_le_leading (sectionCount : BitVec 16)
    {count : Nat} (withinLeading : count ≤ 70) :
    (writeHeaderPrefix sectionCount).take count =
      writeHeaderPrefixLeading.take count := by
  apply Vec.toList_injective
  change List.take count
      (writeHeaderPrefixLeading.toList ++
        ((writeLittleEndian (count := 2) sectionCount).toList ++
          writeHeaderPrefixTrailing.toList)) =
    List.take count writeHeaderPrefixLeading.toList
  rw [List.take_append_of_le_length]
  change count ≤ writeHeaderPrefixLeading.length
  simpa using withinLeading

/-- Pad the at-most-two section-count bytes present in a partial header to an
exact two-byte little-endian value. Bytes after the count are ignored here. -/
def paddedHeaderSectionCountBytes (input : Std.Logical.ByteArray) :
    Std.Logical.ByteArray :=
  ((input.drop 70) ++ Vec.replicate 2 0).take 2

@[simp] theorem length_paddedHeaderSectionCountBytes
    (input : Std.Logical.ByteArray) :
    (paddedHeaderSectionCountBytes input).length = 2 := by
  simp [paddedHeaderSectionCountBytes]

/-- Recover a total section-count candidate from whatever count bytes are
already present in a partial header, zero-filling only missing bytes. -/
def partialHeaderSectionCount (input : Std.Logical.ByteArray) : BitVec 16 :=
  littleEndianToBitVec
    ⟨paddedHeaderSectionCountBytes input,
      length_paddedHeaderSectionCountBytes input⟩

/-- Re-encoding the recovered partial count returns its exact padded bytes. -/
@[simp] theorem writeLittleEndian_partialHeaderSectionCount
    (input : Std.Logical.ByteArray) :
    writeLittleEndian (count := 2) (partialHeaderSectionCount input) =
      paddedHeaderSectionCountBytes input := by
  change (bitVecToLittleEndian (littleEndianToBitVec
    ⟨paddedHeaderSectionCountBytes input,
      length_paddedHeaderSectionCountBytes input⟩)).1 = _
  exact congrArg Subtype.val
    (bitVecToLittleEndian_littleEndianToBitVec
      ⟨paddedHeaderSectionCountBytes input,
        length_paddedHeaderSectionCountBytes input⟩)

/-- Through the two-byte count field, the reconstructed canonical header
retains every byte already supplied by the caller. -/
theorem take_reconstructedHeader_through_count
    (input : Std.Logical.ByteArray)
    (pastLeading : 70 ≤ input.length) (withinCount : input.length ≤ 72) :
    (writeHeaderPrefix (partialHeaderSectionCount input)).take input.length =
      writeHeaderPrefixLeading ++ input.drop 70 := by
  let countBytes := writeLittleEndian (count := 2)
    (partialHeaderSectionCount input)
  have countBytesLength : countBytes.length = 2 := by simp [countBytes]
  have splitLength : 70 + (input.length - 70) = input.length := by omega
  have remainingCount : input.length - 70 ≤ 2 := by omega
  have leadingTaken : writeHeaderPrefixLeading.take 70 =
      writeHeaderPrefixLeading := by
    simpa using Vec.take_length writeHeaderPrefixLeading
  have takeCountAppend :
      (countBytes ++ writeHeaderPrefixTrailing).take (input.length - 70) =
        countBytes.take (input.length - 70) := by
    apply Vec.toList_injective
    change List.take (input.length - 70)
        (countBytes.toList ++ writeHeaderPrefixTrailing.toList) =
      List.take (input.length - 70) countBytes.toList
    rw [List.take_append_of_le_length]
    change input.length - 70 ≤ countBytes.length
    simpa [countBytesLength] using remainingCount
  have takePadded :
      (paddedHeaderSectionCountBytes input).take (input.length - 70) =
        input.drop 70 := by
    unfold paddedHeaderSectionCountBytes
    rw [Vec.take_take]
    rw [Nat.min_eq_left remainingCount]
    apply Vec.take_append_of_length_eq
    simp
  calc
    (writeHeaderPrefix (partialHeaderSectionCount input)).take input.length =
        (writeHeaderPrefix (partialHeaderSectionCount input)).take
          (70 + (input.length - 70)) := by rw [splitLength]
    _ = (writeHeaderPrefix (partialHeaderSectionCount input)).take 70 ++
        ((writeHeaderPrefix (partialHeaderSectionCount input)).drop 70).take
          (input.length - 70) := Vec.take_add _ _ _
    _ = writeHeaderPrefixLeading ++
        (countBytes ++ writeHeaderPrefixTrailing).take
          (input.length - 70) := by
      rw [take_writeHeaderPrefix_of_le_leading _ (by omega)]
      unfold writeHeaderPrefix
      rw [Vec.append_assoc]
      rw [Vec.drop_append_of_length_eq length_writeHeaderPrefixLeading]
      rw [leadingTaken]
    _ = writeHeaderPrefixLeading ++
        countBytes.take
          (input.length - 70) := by
      rw [takeCountAppend]
    _ = writeHeaderPrefixLeading ++
        (paddedHeaderSectionCountBytes input).take
          (input.length - 70) := by
      dsimp [countBytes]
      rw [writeLittleEndian_partialHeaderSectionCount]
    _ = writeHeaderPrefixLeading ++ input.drop 70 := by
      rw [takePadded]

/-- `take_reconstructedHeader_count_boundary` states that once both count
bytes are present, reconstructing the count preserves those exact bytes. -/
theorem take_reconstructedHeader_count_boundary
    (input : Std.Logical.ByteArray) (hasCount : 72 ≤ input.length) :
    (writeHeaderPrefix (partialHeaderSectionCount input)).take 72 =
      writeHeaderPrefixLeading ++ (input.drop 70).take 2 := by
  let countBytes := writeLittleEndian (count := 2)
    (partialHeaderSectionCount input)
  have dropHasCount : 2 ≤ (input.drop 70).length := by
    simp
    omega
  have paddedEq : paddedHeaderSectionCountBytes input =
      (input.drop 70).take 2 := by
    unfold paddedHeaderSectionCountBytes
    apply Vec.toList_injective
    change List.take 2 ((input.drop 70).toList ++ (Vec.replicate 2 0).toList) =
      List.take 2 (input.drop 70).toList
    rw [List.take_append_of_le_length]
    change 2 ≤ (input.drop 70).length
    exact dropHasCount
  have leadingTaken : writeHeaderPrefixLeading.take 70 =
      writeHeaderPrefixLeading := by
    simpa using Vec.take_length writeHeaderPrefixLeading
  calc
    (writeHeaderPrefix (partialHeaderSectionCount input)).take 72 =
        (writeHeaderPrefix (partialHeaderSectionCount input)).take (70 + 2) := rfl
    _ = (writeHeaderPrefix (partialHeaderSectionCount input)).take 70 ++
        ((writeHeaderPrefix (partialHeaderSectionCount input)).drop 70).take 2 :=
      Vec.take_add _ _ _
    _ = writeHeaderPrefixLeading ++
        (countBytes ++ writeHeaderPrefixTrailing).take 2 := by
      rw [take_writeHeaderPrefix_of_le_leading _ (by omega)]
      unfold writeHeaderPrefix
      rw [Vec.append_assoc]
      rw [Vec.drop_append_of_length_eq length_writeHeaderPrefixLeading]
      rw [leadingTaken]
    _ = writeHeaderPrefixLeading ++ countBytes := by
      rw [Vec.take_append_of_length_eq]
      simp [countBytes]
    _ = writeHeaderPrefixLeading ++ paddedHeaderSectionCountBytes input := by
      dsimp [countBytes]
      rw [writeLittleEndian_partialHeaderSectionCount]
    _ = writeHeaderPrefixLeading ++ (input.drop 70).take 2 := by
      rw [paddedEq]

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

/-- Every compatible input is literally a prefix of the canonical header
obtained by retaining its supplied section-count bytes. -/
theorem compatible_is_canonical_prefix (input : Std.Logical.ByteArray)
    (compatible : headerPrefixCompatible input = true) :
    input = (writeHeaderPrefix (partialHeaderSectionCount input)).take input.length := by
  unfold headerPrefixCompatible at compatible
  split at compatible
  next withinLeading =>
    have fixed : input = writeHeaderPrefixLeading.take input.length :=
      of_decide_eq_true compatible
    exact fixed.trans
      (take_writeHeaderPrefix_of_le_leading
        (partialHeaderSectionCount input) withinLeading).symm
  next beyondLeading =>
    split at compatible
    next withinCount =>
      have fixed : input.take 70 = writeHeaderPrefixLeading :=
        of_decide_eq_true compatible
      calc
        input = input.take 70 ++ input.drop 70 :=
          (Vec.append_splitAt input 70).symm
        _ = writeHeaderPrefixLeading ++ input.drop 70 := by rw [fixed]
        _ = (writeHeaderPrefix (partialHeaderSectionCount input)).take
            input.length :=
          (take_reconstructedHeader_through_count input
            (by omega) withinCount).symm
    next beyondCount =>
      have booleanParts := Bool.and_eq_true_iff.mp compatible
      have fixedParts :
          input.take 70 = writeHeaderPrefixLeading ∧
            input.drop 72 = writeHeaderPrefixTrailing.take (input.length - 72) :=
        ⟨of_decide_eq_true booleanParts.1, of_decide_eq_true booleanParts.2⟩
      have throughCount :
          (writeHeaderPrefix (partialHeaderSectionCount input)).take 72 =
            input.take 72 := by
        calc
          (writeHeaderPrefix (partialHeaderSectionCount input)).take 72 =
              writeHeaderPrefixLeading ++ (input.drop 70).take 2 :=
            take_reconstructedHeader_count_boundary input (by omega)
          _ = input.take 70 ++ (input.drop 70).take 2 := by rw [fixedParts.1]
          _ = input.take (70 + 2) := (Vec.take_add input 70 2).symm
          _ = input.take 72 := rfl
      have headerDrop :
          (writeHeaderPrefix (partialHeaderSectionCount input)).drop 72 =
            writeHeaderPrefixTrailing := by
        unfold writeHeaderPrefix
        apply Vec.drop_append_of_length_eq
        simp
      calc
        input = input.take 72 ++ input.drop 72 :=
          (Vec.append_splitAt input 72).symm
        _ = (writeHeaderPrefix (partialHeaderSectionCount input)).take 72 ++
            writeHeaderPrefixTrailing.take (input.length - 72) := by
          rw [throughCount, fixedParts.2]
        _ = (writeHeaderPrefix (partialHeaderSectionCount input)).take 72 ++
            ((writeHeaderPrefix (partialHeaderSectionCount input)).drop 72).take
              (input.length - 72) := by rw [headerDrop]
        _ = (writeHeaderPrefix (partialHeaderSectionCount input)).take
              (72 + (input.length - 72)) :=
          (Vec.take_add _ 72 (input.length - 72)).symm
        _ = (writeHeaderPrefix (partialHeaderSectionCount input)).take
              input.length := by
          congr 1
          omega

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

/-- Successful executable parsing is exactly the canonical denotation. This
is the two-sided success law required before adding streaming classifications. -/
theorem takeHeaderPrefix_done_iff (input : Std.Logical.ByteArray)
    (sectionCount : BitVec 16) (rest : Std.Logical.ByteArray) :
    takeHeaderPrefix input = .done sectionCount rest ↔
      input = writeHeaderPrefix sectionCount ++ rest := by
  constructor
  · intro parsed
    unfold takeHeaderPrefix at parsed
    split at parsed
    next enough =>
      dsimp at parsed
      split at parsed
      next parsedCount =>
        split at parsed
        next canonical =>
          injection parsed with countEquality restEquality
          subst sectionCount
          subst rest
          rw [← canonical]
          exact Vec.append_splitAt input headerPrefixSize |>.symm
        next => contradiction
      next => contradiction
    next =>
      split at parsed <;> contradiction
  · intro equality
    subst input
    exact takeHeaderPrefix_writeHeaderPrefix_append sectionCount rest

/-- The executable incomplete result is exactly the compatible-short case and
retains the precise byte deficit. -/
theorem takeHeaderPrefix_needMore_iff (input : Std.Logical.ByteArray)
    (hint : Option Nat) :
    takeHeaderPrefix input = .needMore hint ↔
      input.length < headerPrefixSize ∧
      headerPrefixCompatible input = true ∧
      hint = some (headerPrefixSize - input.length) := by
  unfold takeHeaderPrefix
  split
  next enough =>
    dsimp
    split
    next => split <;> simp [Nat.not_lt_of_ge enough]
    next => simp [Nat.not_lt_of_ge enough]
  next notEnough =>
    split
    next compatible =>
      simp [Nat.lt_of_not_ge notEnough, compatible, eq_comm]
    next incompatible => simp [incompatible]

/-- Every executable `needMore` result names an exact deficit that really does
complete to a canonical header. This rules out streaming parsers that defer an
already-impossible prefix forever. -/
theorem takeHeaderPrefix_needMore_has_exact_completion
    (input : Std.Logical.ByteArray) (hint : Option Nat)
    (parsed : takeHeaderPrefix input = .needMore hint) :
    ∃ suffix sectionCount,
      suffix.length = headerPrefixSize - input.length ∧
      takeHeaderPrefix (input ++ suffix) =
        .done sectionCount Vec.empty := by
  have classification := (takeHeaderPrefix_needMore_iff input hint).mp parsed
  have compatible := classification.2.1
  let sectionCount := partialHeaderSectionCount input
  let complete := writeHeaderPrefix sectionCount
  let suffix := complete.drop input.length
  have inputPrefix : input = complete.take input.length := by
    exact compatible_is_canonical_prefix input compatible
  have completed : input ++ suffix = complete := by
    rw [inputPrefix]
    exact Vec.append_splitAt complete input.length
  refine ⟨suffix, sectionCount, ?_, ?_⟩
  · simp [suffix, complete, headerPrefixSize]
  · rw [completed]
    exact takeHeaderPrefix_writeHeaderPrefix sectionCount

end Grass.Artifact.PE
