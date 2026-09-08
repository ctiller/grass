import Grass.Artifact.Binary.Endian

/-!
# Deterministic `.gobj` length framing

`U32LengthPrefixedBytes` is the allocation-safe variable-width framing used by
the proof-free `.gobj` schema. Its writer records a little-endian byte count,
and `readU32LengthPrefixedBytes` validates that count before slicing input.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Bytes whose length is representable by the `.gobj` 32-bit framing field. -/
structure U32LengthPrefixedBytes where
  bytes : Std.Logical.ByteArray
  lengthFits : bytes.length < 2 ^ 32
deriving DecidableEq, Repr

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
  | .needMore hint => .needMore hint
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

end Grass.Artifact.Binary.Gobj
