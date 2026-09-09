import Grass.Artifact.Binary.Endian

/-! # Compositional endian reader/writer laws

These laws retain arbitrary suffixes and exact short-input deficits without
requiring format consumers to unfold the endian implementations.
-/

namespace Grass.Artifact.Binary

open Grass.Std.Logical Grass.Grammar

/-- `takeLittleEndian_writeLittleEndian_append` preserves every trailing byte. -/
@[simp] theorem takeLittleEndian_writeLittleEndian_append {count : Nat}
    (value : BitVec (8 * count)) (rest : Std.Logical.ByteArray) :
    takeLittleEndian count (writeLittleEndian value ++ rest) = .done value rest := by
  simp [takeLittleEndian, writeLittleEndian, isoParser, isoWriter,
    ParseResult.map, littleEndianIsomorphism]

/-- `takeBigEndian_writeBigEndian_append` preserves every trailing byte. -/
@[simp] theorem takeBigEndian_writeBigEndian_append {count : Nat}
    (value : BitVec (8 * count)) (rest : Std.Logical.ByteArray) :
    takeBigEndian count (writeBigEndian value ++ rest) = .done value rest := by
  simp [takeBigEndian, writeBigEndian, isoParser, isoWriter,
    ParseResult.map, bigEndianIsomorphism]

/-- `takeLittleEndian_short` returns the exact missing byte count. -/
theorem takeLittleEndian_short {count : Nat} {input : Std.Logical.ByteArray}
    (short : input.length < count) :
    takeLittleEndian count input = .needMore (some (count - input.length)) := by
  simp [takeLittleEndian, isoParser, takeExactSized_short short, ParseResult.map]

/-- `takeBigEndian_short` returns the exact missing byte count. -/
theorem takeBigEndian_short {count : Nat} {input : Std.Logical.ByteArray}
    (short : input.length < count) :
    takeBigEndian count input = .needMore (some (count - input.length)) := by
  simp [takeBigEndian, isoParser, takeExactSized_short short, ParseResult.map]

/-- `length_writeBigEndian` identifies the type-indexed emitted byte count. -/
@[simp] theorem length_writeBigEndian {count : Nat} (value : BitVec (8 * count)) :
    (writeBigEndian value).length = count :=
  (bitVecToBigEndian value).2

end Grass.Artifact.Binary
