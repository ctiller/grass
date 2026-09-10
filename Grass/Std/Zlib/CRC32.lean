import Grass.Std.Logical.Vec

/-!
# Reflected CRC-32

An executable CRC core for the gzip checksum model. It keeps bytes in the logical
`ByteArray` representation and states the branch-free recurrence used by the
x86 implementation next to the conditional RFC recurrence.

RFC 1952 §8: https://www.rfc-editor.org/rfc/rfc1952#section-8
-/

namespace Grass.Std.Zlib.CRC32

open Grass.Std.Logical

/-- One reflected CRC bit, in the conditional form from RFC 1952. -/
def bitStep (poly c : BitVec 32) : BitVec 32 :=
  if c &&& 1 != 0 then (c >>> 1) ^^^ poly else c >>> 1

/-- One reflected CRC bit, using the all-zero/all-one feedback mask. -/
def maskBitStep (poly c : BitVec 32) : BitVec 32 :=
  (c >>> 1) ^^^ (poly &&& (0 - (c &&& 1)))

private theorem lowBit_cases (c : BitVec 32) : c &&& 1 = 0 ∨ c &&& 1 = 1 := by
  have h : c.toNat % 2 = 0 ∨ c.toNat % 2 = 1 := by omega
  rcases h with h | h
  · left
    apply BitVec.toNat_inj.mp
    simp [BitVec.toNat_and, BitVec.toNat_one (show 0 < 32 by omega), Nat.and_one_is_mod, h]
  · right
    apply BitVec.toNat_inj.mp
    simp [BitVec.toNat_and, BitVec.toNat_one (show 0 < 32 by omega), Nat.and_one_is_mod, h]

theorem bitStep_eq_maskBitStep (poly c : BitVec 32) :
    bitStep poly c = maskBitStep poly c := by
  unfold bitStep maskBitStep
  rcases lowBit_cases c with h | h
  · rw [h]
    simp
  · rw [h]
    have hneg : (0 - (1 : BitVec 32)) = -1 := BitVec.zero_sub _
    rw [hneg]
    have hall : (-1 : BitVec 32) = BitVec.allOnes 32 := BitVec.neg_one_eq_allOnes
    have hand : poly &&& (-1 : BitVec 32) = poly := by rw [hall]; exact BitVec.and_allOnes
    have hne : (1 : BitVec 32) != 0 := by decide
    rw [if_pos hne, hand]

def eightSteps (poly c : BitVec 32) : BitVec 32 :=
  bitStep poly (bitStep poly (bitStep poly (bitStep poly
    (bitStep poly (bitStep poly (bitStep poly (bitStep poly c)))))))

def eightMaskSteps (poly c : BitVec 32) : BitVec 32 :=
  maskBitStep poly (maskBitStep poly (maskBitStep poly (maskBitStep poly
    (maskBitStep poly (maskBitStep poly (maskBitStep poly (maskBitStep poly c)))))))

theorem eightSteps_eq_eightMaskSteps (poly c : BitVec 32) :
    eightSteps poly c = eightMaskSteps poly c := by
  simp only [eightSteps, eightMaskSteps, bitStep_eq_maskBitStep]

def injectByte (c : BitVec 32) (byte : Byte) : BitVec 32 := c ^^^ byte.zeroExtend 32

def byteStep (poly : BitVec 32) (c : BitVec 32) (byte : Byte) : BitVec 32 :=
  eightSteps poly (injectByte c byte)

def maskByteStep (poly : BitVec 32) (c : BitVec 32) (byte : Byte) : BitVec 32 :=
  eightMaskSteps poly (injectByte c byte)

theorem byteStep_eq_maskByteStep (poly c : BitVec 32) (byte : Byte) :
    byteStep poly c byte = maskByteStep poly c byte :=
  eightSteps_eq_eightMaskSteps poly (injectByte c byte)

def updateRaw (poly : BitVec 32) (c : BitVec 32) (bytes : Grass.Std.Logical.ByteArray) : BitVec 32 :=
  Vec.foldl (byteStep poly) c bytes

def maskedUpdateRaw (poly : BitVec 32) (c : BitVec 32)
    (bytes : Grass.Std.Logical.ByteArray) : BitVec 32 :=
  Vec.foldl (maskByteStep poly) c bytes

theorem updateRaw_eq_maskedUpdateRaw (poly c : BitVec 32) (bytes : Grass.Std.Logical.ByteArray) :
    updateRaw poly c bytes = maskedUpdateRaw poly c bytes := by
  induction bytes using Vec.recOnCons generalizing c with
  | empty => rfl
  | cons byte rest ih =>
    simp only [updateRaw, maskedUpdateRaw, Vec.foldl_cons]
    rw [byteStep_eq_maskByteStep]
    exact ih _

theorem updateRaw_append (poly c : BitVec 32)
    (left right : Grass.Std.Logical.ByteArray) :
    updateRaw poly c (left ++ right) = updateRaw poly (updateRaw poly c left) right := by
  simp [updateRaw, Vec.foldl, List.foldl_append]

def polynomial : BitVec 32 := 0xedb88320
def initial : BitVec 32 := 0xffffffff

def checksum (bytes : Grass.Std.Logical.ByteArray) : BitVec 32 :=
  updateRaw polynomial initial bytes ^^^ 0xffffffff

theorem checksum_append (left right : Grass.Std.Logical.ByteArray) :
    checksum (left ++ right) = updateRaw polynomial (checksum left ^^^ 0xffffffff) right ^^^ 0xffffffff := by
  unfold checksum
  rw [updateRaw_append]
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end Grass.Std.Zlib.CRC32
