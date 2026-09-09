import Grass.Artifact.Binary.Endian

/-!
# Deterministic `.gobj` length framing

`U32LengthPrefixedBytes` is the allocation-safe variable-width framing used by
the proof-free `.gobj` schema. Its writer records a little-endian byte count,
and `readU32LengthPrefixedBytes` validates that count before slicing input.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

universe u

/-- Add bytes that are unconditionally required after the currently incomplete
field. Unknown requirements remain unknown, while successful and invalid
results are unchanged. -/
def requireAfter {α : Type u} (minimumAfter : Nat) :
    ParseResult α → ParseResult α
  | .done value suffix => .done value suffix
  | .needMore (some minimumAdditional) =>
      .needMore (some (minimumAdditional + minimumAfter))
  | .needMore none => .needMore none
  | .invalid error => .invalid error

/-- `requireAfter_needMore_ne_done` proves that adding a downstream minimum to
an incomplete parse cannot manufacture a successful result. -/
@[simp] theorem requireAfter_needMore_ne_done {α : Type u}
    (minimumAfter : Nat) (hint : Option Nat) (value : α)
    (rest : Std.Logical.ByteArray) :
    requireAfter minimumAfter (.needMore hint) ≠ .done value rest := by
  cases hint <;> simp [requireAfter]

/-- Bytes whose length is representable by the `.gobj` 32-bit framing field. -/
structure U32LengthPrefixedBytes where
  bytes : Std.Logical.ByteArray
  lengthFits : bytes.length < 2 ^ 32
deriving DecidableEq, Repr

/-- Independent typed language for a canonical 32-bit little-endian byte
length followed by exactly that many unconstrained bytes. -/
def u32LengthPrefixedBytesFormat : Format U32LengthPrefixedBytes :=
  .lift
    (.seq (littleEndianFormat 4) fun count =>
      repeatedBytesFormat count.toNat)
    fun value => (BitVec.ofNat 32 value.bytes.length, value.bytes)

/-- Retain the checked width of bytes read under a particular 32-bit count. -/
def u32LengthPrefixedOfSized (count : BitVec 32)
    (bytes : SizedByteArray count.toNat) : U32LengthPrefixedBytes where
  bytes := bytes.1
  lengthFits := by
    rw [bytes.2]
    simpa using BitVec.isLt count

/-- Serialize a 32-bit little-endian byte count followed by the exact bytes. -/
def writeU32LengthPrefixedBytes (value : U32LengthPrefixedBytes) :
    Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (BitVec.ofNat 32 value.bytes.length) ++
    value.bytes

/-- `writeU32LengthPrefixedBytes_ofSized` states that re-serializing bytes
retained under a parsed count preserves that exact count and payload. -/
@[simp] theorem writeU32LengthPrefixedBytes_ofSized (count : BitVec 32)
    (bytes : SizedByteArray count.toNat) :
    writeU32LengthPrefixedBytes (u32LengthPrefixedOfSized count bytes) =
      writeLittleEndian (count := 4) count ++ bytes.1 := by
  unfold writeU32LengthPrefixedBytes u32LengthPrefixedOfSized
  have countRoundTrip : BitVec.ofNat 32 bytes.1.length = count := by
    apply BitVec.toNat_inj.mp
    rw [BitVec.toNat_ofNat, bytes.2]
    exact Nat.mod_eq_of_lt (by simpa using BitVec.isLt count)
  rw [countRoundTrip]

/-- `derives_u32LengthPrefixedBytes_iff` characterizes the independent format
by the canonical writer bytes and an arbitrary retained suffix. -/
theorem derives_u32LengthPrefixedBytes_iff
    {input rest : Std.Logical.ByteArray} {value : U32LengthPrefixedBytes} :
    Derives u32LengthPrefixedBytesFormat input value rest ↔
      input = writeU32LengthPrefixedBytes value ++ rest := by
  have countEq : (BitVec.ofNat 32 value.bytes.length).toNat =
      value.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.lengthFits]
  constructor
  · intro derivation
    have sequence := derivation.lift_inner
    rcases sequence.seqOuterShape with
      ⟨middle, count, bytes, pairEq, countDerivation, bytesDerivation⟩
    injection pairEq with countValue bytesValue
    subst count
    subst bytes
    have countInput := derives_littleEndianFormat_iff.mp countDerivation
    have bytesInput := (derives_repeatedBytes_iff.mp bytesDerivation).1
    rw [countInput, bytesInput]
    simp [writeU32LengthPrefixedBytes, Vec.append_assoc]
  · intro equality
    rw [equality]
    apply Derives.lift
    apply Derives.seq
    · exact (writeLittleEndian_realizes 4).derivesWithSuffix
        (BitVec.ofNat 32 value.bytes.length) (value.bytes ++ rest)
    · simpa [countEq] using anyBytes_derives value.bytes rest

/-- Read a checked 32-bit little-endian byte count and its exact payload. -/
def readU32LengthPrefixedBytes (input : Std.Logical.ByteArray) :
    ParseResult U32LengthPrefixedBytes :=
  match takeLittleEndian 4 input with
  | .done count rest =>
    match takeExactSized count.toNat rest with
    | .done bytes suffix =>
      .done (u32LengthPrefixedOfSized count bytes) suffix
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore _ => .needMore none
  | .invalid error => .invalid error

/-- The framing width is four bytes plus the exact payload length. -/
@[simp] theorem length_writeU32LengthPrefixedBytes
    (value : U32LengthPrefixedBytes) :
    (writeU32LengthPrefixedBytes value).length = 4 + value.bytes.length := by
  simp [writeU32LengthPrefixedBytes]

/-- `readU32LengthPrefixedBytes_write_append` parses a framed value exactly and
preserves every following suffix. -/
@[simp] theorem readU32LengthPrefixedBytes_write_append
    (value : U32LengthPrefixedBytes) (suffix : Std.Logical.ByteArray) :
    readU32LengthPrefixedBytes
        (writeU32LengthPrefixedBytes value ++ suffix) =
      .done value suffix := by
  have countEq : (BitVec.ofNat 32 value.bytes.length).toNat =
      value.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.lengthFits]
  let count : BitVec 32 := BitVec.ofNat 32 value.bytes.length
  let sized : SizedByteArray count.toNat := ⟨value.bytes, countEq.symm⟩
  unfold readU32LengthPrefixedBytes writeU32LengthPrefixedBytes
  rw [Vec.append_assoc]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only
  change (match takeExactSized count.toNat (writeExact sized ++ suffix) with
    | .done bytes rest =>
      ParseResult.done (u32LengthPrefixedOfSized count bytes) rest
    | .needMore hint => ParseResult.needMore hint
    | .invalid error => ParseResult.invalid error) = _
  rw [takeExactSized_writeExact_append]
  simp only
  apply congrArg (fun bytes => ParseResult.done bytes suffix)
  cases value
  rfl

/-- Complete framed values are the empty-suffix instance of the prefix law. -/
@[simp] theorem readU32LengthPrefixedBytes_write
    (value : U32LengthPrefixedBytes) :
    readU32LengthPrefixedBytes (writeU32LengthPrefixedBytes value) =
      .done value Vec.empty := by
  simpa using readU32LengthPrefixedBytes_write_append value Vec.empty

/-- Successful parsing of arbitrary input is equivalent to the independent
format denotation, not merely to a writer-generated round trip. -/
theorem readU32LengthPrefixedBytes_done_iff
    (input : Std.Logical.ByteArray) (value : U32LengthPrefixedBytes)
    (rest : Std.Logical.ByteArray) :
    readU32LengthPrefixedBytes input = .done value rest ↔
      Derives u32LengthPrefixedBytesFormat input value rest := by
  rw [derives_u32LengthPrefixedBytes_iff]
  constructor
  · intro parsed
    unfold readU32LengthPrefixedBytes at parsed
    split at parsed
    next count afterCount countParsed =>
      split at parsed
      next bytes suffix bytesParsed =>
        injection parsed with valueEquality restEquality
        subst value
        subst rest
        have countInput := derives_littleEndianFormat_iff.mp
          ((takeLittleEndian_realizes 4).successSound
            input count afterCount countParsed)
        have bytesFixed := (takeExactSized_realizes count.toNat).successSound
          afterCount bytes suffix bytesParsed
        have bytesInput := (derives_repeatedBytes_iff.mp
          (derives_fixedBytes_iff.mp bytesFixed)).1
        calc
          input = writeLittleEndian count ++ afterCount := countInput
          _ = writeLittleEndian count ++ (bytes.1 ++ suffix) := by rw [bytesInput]
          _ = (writeLittleEndian count ++ bytes.1) ++ suffix :=
            (Vec.append_assoc _ _ _).symm
          _ = writeU32LengthPrefixedBytes
                (u32LengthPrefixedOfSized count bytes) ++ suffix := by
            rw [writeU32LengthPrefixedBytes_ofSized]
      next => contradiction
      next => contradiction
    next => contradiction
    next => contradiction
  · intro canonical
    rw [canonical]
    exact readU32LengthPrefixedBytes_write_append value rest

end Grass.Artifact.Binary.Gobj
