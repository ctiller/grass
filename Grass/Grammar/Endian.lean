import Grass.Grammar.Binary

/-!
# Total endian views of sized bytes

Endian conversion starts only after byte length is present in the value type.
The recursive list operations below are executable and retain exact bit widths.
They are the proof-bearing foundation for the public isomorphisms; no malformed
length can reach either conversion.
-/

namespace Grass.Grammar

open Grass.Std.Logical

/-- Pack bytes in most-significant-first order. -/
def packBigList : (bytes : List Byte) → BitVec (8 * bytes.length)
  | [] => 0#0
  | byte :: rest =>
      (byte ++ packBigList rest).cast (by simp [Nat.mul_succ]; omega)

/-- Split a bitvector into most-significant-first bytes. -/
def unpackBigList : (count : Nat) → BitVec (8 * count) → List Byte
  | 0, _ => []
  | count + 1, value =>
      value.extractLsb' (8 * count) 8 ::
        unpackBigList count (value.extractLsb' 0 (8 * count))

@[simp] theorem length_unpackBigList (count : Nat) (value : BitVec (8 * count)) :
    (unpackBigList count value).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [unpackBigList, ih]

/-- Splitting a recursively packed big-endian list returns that exact list. -/
@[simp] theorem unpackBigList_packBigList (bytes : List Byte) :
    unpackBigList bytes.length (packBigList bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
      simp only [packBigList, unpackBigList, List.length_cons]
      congr 1
      · rw [BitVec.extractLsb'_cast]
        exact BitVec.extractLsb'_append_eq_left
      · rw [BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_right]
        exact ih

/-- `toNat_packBigList_unpackBigList` states that recursively packing a split
bitvector preserves its unsigned value. -/
theorem toNat_packBigList_unpackBigList (count : Nat) (value : BitVec (8 * count)) :
    (packBigList (unpackBigList count value)).toNat = value.toNat := by
  induction count with
  | zero =>
      calc
        (packBigList (unpackBigList 0 value)).toNat = 0 := rfl
        _ = value.toNat := (BitVec.toNat_zero_length value).symm
  | succ count ih =>
      simp only [unpackBigList, packBigList, BitVec.toNat_cast, BitVec.toNat_append]
      rw [ih]
      rw [length_unpackBigList]
      let reshaped : BitVec (8 + 8 * count) := value.cast (by omega)
      have rebuilt :
          value.extractLsb' (8 * count) 8 ++ value.extractLsb' 0 (8 * count) = reshaped := by
        simpa only [reshaped, BitVec.extractLsb'_cast] using
          (BitVec.extractLsb'_append_extractLsb' (x := reshaped))
      rw [← BitVec.toNat_append]
      calc
        _ = reshaped.toNat := congrArg BitVec.toNat rebuilt
        _ = value.toNat := BitVec.toNat_cast _ _

/-- `packBigList_unpackBigList` states that recursively packing a split
bitvector preserves every bit. -/
@[simp] theorem packBigList_unpackBigList (count : Nat) (value : BitVec (8 * count)) :
    (packBigList (unpackBigList count value)).cast
        (congrArg (fun n => 8 * n) (length_unpackBigList count value)) = value := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_cast]
  exact toNat_packBigList_unpackBigList count value

/-- Interpret sized bytes as a big-endian integer bitvector. -/
def bigEndianToBitVec {count : Nat} (bytes : SizedByteArray count) :
    BitVec (8 * count) :=
  (packBigList bytes.1.toList).cast (congrArg (fun n => 8 * n) bytes.2)

/-- Split a bitvector into a sized big-endian byte sequence. -/
def bitVecToBigEndian {count : Nat} (value : BitVec (8 * count)) :
    SizedByteArray count :=
  ⟨Vec.fromList (unpackBigList count value), by simp⟩

/-- `bitVecToBigEndian_bigEndianToBitVec` states that packing after splitting
preserves every sized byte exactly. -/
theorem bitVecToBigEndian_bigEndianToBitVec {count : Nat}
    (bytes : SizedByteArray count) :
    bitVecToBigEndian (bigEndianToBitVec bytes) = bytes := by
  rcases bytes with ⟨bytes, rfl⟩
  apply SizedVec.ext
  apply Vec.toList_injective
  simp only [bitVecToBigEndian, Vec.toList_fromList]
  have packedEq :
      bigEndianToBitVec (⟨bytes, rfl⟩ : SizedByteArray bytes.length) =
        packBigList bytes.toList := by
    apply BitVec.toNat_inj.mp
    exact BitVec.toNat_cast _ _
  rw [packedEq]
  exact unpackBigList_packBigList bytes.toList

/-- `bigEndianToBitVec_bitVecToBigEndian` states that splitting and then packing
preserves every fixed-width bitvector. -/
@[simp] theorem bigEndianToBitVec_bitVecToBigEndian {count : Nat}
    (value : BitVec (8 * count)) :
    bigEndianToBitVec (bitVecToBigEndian value) = value := by
  apply BitVec.toNat_inj.mp
  simp only [bigEndianToBitVec, bitVecToBigEndian, Vec.toList_fromList]
  exact toNat_packBigList_unpackBigList count value

/-- Total big-endian view of a fixed byte sequence as an integer bitvector. -/
def bigEndianIsomorphism (count : Nat) :
    Isomorphism (SizedByteArray count) (BitVec (8 * count)) where
  forward := bigEndianToBitVec
  backward := bitVecToBigEndian
  backward_forward := bitVecToBigEndian_bigEndianToBitVec
  forward_backward := bigEndianToBitVec_bitVecToBigEndian

/-- Fixed-width bytes interpreted as a big-endian integer value. -/
def bigEndianFormat (count : Nat) : Format (BitVec (8 * count)) :=
  (fixedBytesFormat count).iso (bigEndianIsomorphism count)

end Grass.Grammar
