/-!
# LEB128 codec for the Wasm instruction encoding

The Wasm binary format encodes every integer immediate (indices, memarg
fields, `i32.const`/`i64.const` operands) as LEB128: unsigned for indices and
counts, signed for constant operands. This module carries both directions and
their round-trip theorems, ported from `gasm`'s `Gasm.Targets.Wasm.LEB128`
(same Lean toolchain) onto `List UInt8` directly so it composes with
`Grass.Target.ISA.decode : List UInt8 → Option (Instr × Nat)` without a
`ByteArray` detour.

Every decoder here is written in "remainder" style: it consumes a prefix of
its input and returns what is left, so instruction decoding composes decoders
with plain `do`-notation and the round-trip theorems compose with `rw`.
-/
namespace Grass.ISA.Wasm.Target

/-- Encode an unsigned integer as LEB128, least-significant group first. -/
def encodeU (n : Nat) : List UInt8 :=
  let low := n % 128
  if n < 128 then
    [low.toUInt8]
  else
    (low + 128).toUInt8 :: encodeU (n / 128)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Decode one LEB128-encoded unsigned integer from the front of `bytes`,
returning the value and the unconsumed remainder. `none` on a truncated
(unterminated) encoding. -/
def decodeUAux : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    let bn := b.toNat
    if bn < 128 then
      some (bn, rest)
    else
      match decodeUAux rest with
      | none => none
      | some (hi, rest') => some (bn % 128 + 128 * hi, rest')

theorem decodeUAux_encodeU (n : Nat) (rest : List UInt8) :
    decodeUAux (encodeU n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold encodeU
    by_cases h : n < 128
    · simp only [h, if_pos, List.cons_append, List.nil_append]
      show decodeUAux ((n % 128).toUInt8 :: rest) = some (n, rest)
      unfold decodeUAux
      have hbn : ((n % 128).toUInt8).toNat = n % 128 := by
        simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
        omega
      have hn : n % 128 = n := Nat.mod_eq_of_lt h
      rw [hbn, hn]
      simp [h]
    · simp only [h, if_neg, not_false_iff, List.cons_append]
      show decodeUAux (((n % 128) + 128).toUInt8 :: (encodeU (n / 128) ++ rest))
          = some (n, rest)
      unfold decodeUAux
      have hbn : (((n % 128) + 128).toUInt8).toNat = (n % 128) + 128 := by
        simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
        omega
      rw [hbn]
      have hnot : ¬ ((n % 128) + 128 < 128) := by omega
      simp only [hnot, if_neg, not_false_iff]
      have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      have heq : (n % 128 + 128) % 128 + 128 * (n / 128) = n := by omega
      simp only [ih (n / 128) hlt, heq]

theorem encodeU_length_pos (n : Nat) : 0 < (encodeU n).length := by
  unfold encodeU
  dsimp only
  split <;> simp

/-- Decode `count` consecutive LEB128 unsigned integers, e.g. a `br_table`
label vector. -/
def decodeUVec : Nat → List UInt8 → Option (List Nat × List UInt8)
  | 0, bytes => some ([], bytes)
  | k + 1, bytes =>
      match decodeUAux bytes with
      | none => none
      | some (v, rest) =>
          match decodeUVec k rest with
          | none => none
          | some (vs, rest') => some (v :: vs, rest')

theorem decodeUVec_encode (xs : List Nat) (rest : List UInt8) :
    decodeUVec xs.length ((xs.map encodeU).flatten ++ rest) = some (xs, rest) := by
  induction xs generalizing rest with
  | nil => simp [decodeUVec]
  | cons x xs ih =>
      have assoc : encodeU x ++ (xs.map encodeU).flatten ++ rest
          = encodeU x ++ ((xs.map encodeU).flatten ++ rest) := by
        simp [List.append_assoc]
      simp only [List.length_cons, List.map_cons, List.flatten_cons, assoc]
      rw [decodeUVec]
      simp only [decodeUAux_encodeU x, ih rest]

/-- Encode a signed integer as SLEB128; width-agnostic, no built-in bound. -/
def encodeS (val : Int) : List UInt8 :=
  let low := val % 128
  let n := val / 128
  if (n = 0 ∧ low < 64) ∨ (n = -1 ∧ 64 ≤ low) then
    [low.toNat.toUInt8]
  else
    (low.toNat + 128).toUInt8 :: encodeS n
termination_by val.natAbs
decreasing_by
  simp_wf
  omega

/-- Decode one SLEB128-encoded signed integer from the front of `bytes`. -/
def decodeSAux : List UInt8 → Option (Int × List UInt8)
  | [] => none
  | b :: rest =>
    let bn := b.toNat
    if bn < 128 then
      some ((if bn < 64 then (bn : Int) else (bn : Int) - 128), rest)
    else
      match decodeSAux rest with
      | none => none
      | some (hi, rest') => some ((bn % 128 : Nat) + 128 * hi, rest')

theorem decodeSAux_cons (b : UInt8) (rest : List UInt8) :
    decodeSAux (b :: rest) =
      (if b.toNat < 128 then
        some ((if b.toNat < 64 then (b.toNat : Int) else (b.toNat : Int) - 128), rest)
      else
        match decodeSAux rest with
        | none => none
        | some (hi, rest') => some ((b.toNat % 128 : Nat) + 128 * hi, rest')) := rfl

theorem decodeSAux_encodeS (val : Int) (rest : List UInt8) :
    decodeSAux (encodeS val ++ rest) = some (val, rest) := by
  have main : ∀ (k : Nat) (v : Int), v.natAbs = k →
      decodeSAux (encodeS v ++ rest) = some (v, rest) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hk
      unfold encodeS
      by_cases hstop : (v / 128 = 0 ∧ v % 128 < 64) ∨ (v / 128 = -1 ∧ 64 ≤ v % 128)
      · simp only [hstop, if_pos, List.cons_append, List.nil_append]
        show decodeSAux ((v % 128).toNat.toUInt8 :: rest) = some (v, rest)
        rw [decodeSAux_cons]
        have hlow0 : (0 : Int) ≤ v % 128 := by omega
        have hbn : (((v % 128).toNat).toUInt8).toNat = (v % 128).toNat := by
          simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
          omega
        rw [hbn]
        have hlt128 : (v % 128).toNat < 128 := by omega
        rcases hstop with ⟨hn0, hlt64⟩ | ⟨hnm1, hge64⟩
        · have hbnlt : (v % 128).toNat < 64 := by omega
          simp only [hlt128, hbnlt, if_pos, Option.some.injEq, Prod.mk.injEq, and_true]
          have : ((v % 128).toNat : Int) = v % 128 := Int.toNat_of_nonneg hlow0
          omega
        · have hbnge : ¬ ((v % 128).toNat < 64) := by omega
          simp only [hlt128, hbnge, if_pos, if_neg, not_false_iff, Option.some.injEq,
            Prod.mk.injEq, and_true]
          have : ((v % 128).toNat : Int) = v % 128 := Int.toNat_of_nonneg hlow0
          omega
      · simp only [hstop, if_neg, not_false_iff, List.cons_append]
        show decodeSAux (((v % 128).toNat + 128).toUInt8 :: (encodeS (v / 128) ++ rest))
            = some (v, rest)
        rw [decodeSAux_cons]
        have hlow0 : (0 : Int) ≤ v % 128 := by omega
        have hbn : ((((v % 128).toNat + 128).toUInt8)).toNat = (v % 128).toNat + 128 := by
          simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
          omega
        rw [hbn]
        have hnot128 : ¬ ((v % 128).toNat + 128 < 128) := by omega
        simp only [hnot128, if_neg, not_false_iff]
        have hmeasure : (v / 128).natAbs < k := by omega
        rw [ih (v / 128).natAbs hmeasure (v / 128) rfl]
        have hcast : ((v % 128).toNat : Int) = v % 128 := Int.toNat_of_nonneg hlow0
        have hfinal : (((v % 128).toNat + 128) % 128 : Nat) + 128 * (v / 128) = v := by
          have := hcast
          omega
        simp only [hfinal]
  exact main val.natAbs val rfl

theorem encodeS_length_pos (val : Int) : 0 < (encodeS val).length := by
  unfold encodeS
  dsimp only
  split <;> simp

end Grass.ISA.Wasm.Target
