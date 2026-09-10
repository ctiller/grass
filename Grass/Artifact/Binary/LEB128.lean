/-!
# Unsigned LEB128 varints over `List UInt8`

A base-128 variable-length encoding: each byte carries seven value bits and a
continuation bit (the top bit), least-significant group first. Unlike the
fixed-width little-endian encoders in `Grass.Artifact.Binary.LittleEndian`,
LEB128 never truncates: every natural number, however large, has an encoding,
and the round trip below holds unconditionally, with no bound hypothesis on
the value. That makes it the right choice for a header field with no
independently-fixed width (a section count, a byte length, an address on a
format that does not commit to 32 or 64 bits), and it is the encoding the
WebAssembly binary format uses for exactly this reason.
-/

namespace Grass.Artifact.Binary

/-- Encode `n` as an unsigned LEB128 varint: seven value bits per byte, low
group first, continuation bit (`0x80`) set on every byte but the last. -/
def natToLEB128 (n : Nat) : List UInt8 :=
  if h : n < 128 then
    [UInt8.ofNat n]
  else
    UInt8.ofNat (n % 128 + 128) :: natToLEB128 (n / 128)
termination_by n
decreasing_by
  simp only [Nat.not_lt] at h
  exact Nat.div_lt_self (by omega) (by omega)

/-- Decode one unsigned LEB128 varint from the head of the list, or `none` if
the list ends before a byte without the continuation bit. -/
def readLEB128 : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bytes =>
      if b.toNat < 128 then
        some (b.toNat, bytes)
      else
        match readLEB128 bytes with
        | none => none
        | some (rest, tail) => some (b.toNat - 128 + 128 * rest, tail)

/-- The unconditional round trip: every natural number's LEB128 encoding
decodes back to exactly that number, whatever bytes follow. -/
theorem readLEB128_natToLEB128_append (n : Nat) (rest : List UInt8) :
    readLEB128 (natToLEB128 n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      unfold natToLEB128
      split
      next h =>
        have hlt256 : n < 256 := by omega
        have hb : (UInt8.ofNat n).toNat = n := by
          rw [UInt8.toNat_ofNat']
          exact Nat.mod_eq_of_lt hlt256
        show readLEB128 (UInt8.ofNat n :: rest) = some (n, rest)
        rw [readLEB128, hb, if_pos h]
      next h =>
        simp only [Nat.not_lt] at h
        have hlt256 : n % 128 + 128 < 256 := by omega
        have hb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
          rw [UInt8.toNat_ofNat']
          exact Nat.mod_eq_of_lt hlt256
        have hnot : ¬ n % 128 + 128 < 128 := by omega
        have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
        show readLEB128 (UInt8.ofNat (n % 128 + 128) :: (natToLEB128 (n / 128) ++ rest)) =
          some (n, rest)
        rw [readLEB128, hb, if_neg hnot, ih (n / 128) hdiv]
        show some (n % 128 + 128 - 128 + 128 * (n / 128), rest) = some (n, rest)
        have hval : n % 128 + 128 - 128 + 128 * (n / 128) = n := by omega
        rw [hval]

/-- LEB128 encodes at least one byte; the base case (`n < 128`) encodes
exactly one. -/
theorem natToLEB128_ne_nil (n : Nat) : natToLEB128 n ≠ [] := by
  unfold natToLEB128
  split <;> simp

end Grass.Artifact.Binary
