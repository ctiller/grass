/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean
import Grass.Std.Zlib.Support
import Grass.Std.Zlib.Deflate.Core

namespace Grass.Std.Zlib.Deflate

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Exact bit-reversal involution theorem verified across all 256 possible 8-bit quantities. -/
theorem reverse_bits_8_involutive_inst :
    (Id.run do
      let mut ok := true
      for b in [0:256] do
        if reverseBits (reverseBits b 8) 8 != b then ok := false
      ok) = true := by
  simp [Id.run, reverseBits]
  decide

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Exact length encoding bound preservation verified across all 256 valid length ranges (3..258). -/
theorem encode_length_bounds_inst :
    (Id.run do
      let mut ok := true
      for len in [3:259] do
        let (code, _, _) := encodeLength len
        if code < 257 || code > 285 then ok := false
      ok) = true := by
  simp [Id.run, encodeLength]
  decide

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- One-level unfolding lemma for a decidable-`ite` whose branches are conditionally bounded --
    used to peel `encodeDistance`'s ~26-deep threshold-band `if`/`else` chain one band at a
    time below. Cheap: unlike calling `split` directly on the fully nested chain (which drives
    an internal `simp` congruence pass over the *entire* remaining nested term and exceeds its
    step budget), applying this lemma repeatedly only ever unifies against one `ite` head at a
    time, leaving the (still nested) `else` branch as an opaque metavariable for the next
    application. -/
theorem ite_fst_le {c : Prop} [Decidable c] (a b : Nat × Nat × Nat) (n : Nat)
    (ha : c → a.1 ≤ n) (hb : ¬c → b.1 ≤ n) : (if c then a else b).1 ≤ n := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- `encodeDistance`'s code component never exceeds 29, for every `dist`, not just the
    32768-element sampled range below -- `encodeDistance` is a plain (non-recursive)
    if-then-else chain over ~26 fixed threshold bands, each branch returning a literal code
    in `[0,29]` (or `dist - 1`, when `dist ≤ 4`, itself `≤ 3`); `ite_fst_le` peels one band at
    a time and `omega` closes each resulting leaf, with no enumeration over any of the 32768
    concrete `dist` values. -/
theorem encodeDistance_code_le_29 (dist : Nat) : (encodeDistance dist).1 ≤ 29 := by
  unfold encodeDistance
  repeat' (apply ite_fst_le <;> intro h)
  all_goals omega

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Exact distance encoding bound preservation verified across all 32768 valid distance ranges
    (1..32768). Proven structurally, not by enumeration: plain kernel `decide` on this loop
    times out (`whnf`/`isDefEq` heartbeat exhaustion observed at 32768 iterations, unlike the
    256-element `reverse_bits_8_involutive_inst`/`encode_length_bounds_inst` above, which
    `decide` closes directly). Instead, the `Id.run`/`for` loop is normalized to a plain
    `List.foldl` via Lean's own `forIn_eq_forIn_range'`/`forIn_pure_yield_eq_foldl` simp set
    (the same reformulation `Stdlib/Zlib/CRC32Equivalence.lean`'s `updateCrc32_eq_fold` uses),
    then `foldl_ite_false_of_forall` shows the flag can never flip given
    `encodeDistance_code_le_29` holds for every element -- an `O(1)`-size structural argument
    independent of how many of the 32768 concrete values are visited. -/
theorem encode_distance_bounds_inst :
    (Id.run do
      let mut ok := true
      for dist in [1:32769] do
        let (code, _, _) := encodeDistance dist
        if code > 29 then ok := false
      ok) = true := by
  have foldl_ite_false_of_forall : ∀ (l : List Nat) (p : Nat → Prop) [DecidablePred p],
      (∀ x ∈ l, ¬ p x) → l.foldl (fun ok x => if p x then false else ok) true = true := by
    intro l p _ h
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      have hhd : ¬ p hd := h hd (by simp)
      simp only [List.foldl_cons, if_neg hhd]
      exact ih (fun x hx => h x (by simp [hx]))
  have ite_pure_yield : ∀ {c : Prop} [Decidable c] (a b : Bool),
      (if c then (pure (ForInStep.yield a) : Id (ForInStep Bool)) else pure (ForInStep.yield b)) =
        pure (ForInStep.yield (if c then a else b)) := by
    intro c _ a b; split <;> rfl
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, ite_pure_yield,
    List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  exact foldl_ite_false_of_forall _ (fun dist => (encodeDistance dist).1 > 29)
    (fun dist _ => by have := encodeDistance_code_le_29 dist; omega)

/-
## PA16 token layer: L3 (match certificate) + L4 (self-overlap copy) + token-level L5

Universal, kernel-checked (rung 1, no `native_decide`/`decide` oracle) roundtrip soundness
for the LZ77 layer of DEFLATE — the layer of `decompress` below Huffman coding and
bitstream framing. `tokenize`'s greedy match emission relies only on the total certifying
predicate `matchValid` (the `findLongestMatch` search stays an untrusted heuristic), and
`expandTokens`'s copy loop is byte-for-byte the self-overlap semantics of
`decodeHuffmanStream`'s back-reference loop, so once PA16 P0 (the decoder's `partial def`
conversion) lands, `lz77_roundtrip_soundness` below is the L3/L4/L5 payload the full
`deflate_roundtrip_soundness` composes with the Huffman/bitstream layer (L1/L2).
-/

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- L3: unpacks a `matchValid` certificate into its propositional components — RFC 1951
    range bounds, window containment, and the per-position byte-agreement the copy
    induction (L4) consumes. -/
theorem matchValid_spec {data : ByteArray} {pos len dist : Nat}
    (h : matchValid data pos len dist = true) :
    3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 ∧ dist ≤ pos ∧ pos + len ≤ data.size ∧
    ∀ j, j < len → data.get! (pos - dist + j) = data.get! (pos + j) := by
  simp only [matchValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- The reference copy loop grows the output by exactly the match length. -/
theorem lzCopy_size (dist : Nat) : ∀ (len : Nat) (out : ByteArray),
    (lzCopy dist len out).size = out.size + len := by
  intro len
  induction len with
  | zero => intro out; simp [lzCopy]
  | succ k ih =>
    intro out
    simp only [lzCopy, ih, ByteArray.size_push]
    omega

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- L4, the self-overlapping back-reference copy induction (PA16's hardest sub-lemma,
    `docs/PA16_CODEC_SOUNDNESS.md` §4 L4): if the output so far is exactly `data[0:pos]`
    and the match certificate holds at `pos`, then after copying `len` bytes from `dist`
    back the output is exactly `data[0:pos+len]`. The induction restructures the design
    doc's strong induction into a plain one: at every step the source index `pos - dist`
    lies strictly inside the already-correct prefix (`dist ≥ 1`), so the prefix invariant
    absorbs the `dist < len` self-overlap case with no separate case split — the
    certificate at offset 0 plus a one-position shift of the certificate re-establishes
    the invariant. -/
theorem lzCopy_prefix (data : ByteArray) (dist : Nat) :
    ∀ (len pos : Nat) (out : ByteArray),
      out.size = pos → 1 ≤ dist → dist ≤ pos →
      (∀ i, i < pos → out.get! i = data.get! i) →
      (∀ j, j < len → data.get! (pos - dist + j) = data.get! (pos + j)) →
      ∀ i, i < pos + len → (lzCopy dist len out).get! i = data.get! i := by
  intro len
  induction len with
  | zero =>
    intro pos out hsz _ _ hpref _ i hi
    simp only [lzCopy]
    exact hpref i (by omega)
  | succ k ih =>
    intro pos out hsz hd1 hdp hpref hmatch i hi
    have hsrc : out.get! (out.size - dist) = data.get! pos := by
      have h0 := hmatch 0 (by omega)
      have e1 : pos - dist + 0 = pos - dist := by omega
      have e2 : pos + 0 = pos := by omega
      rw [e1, e2] at h0
      have hlt : out.size - dist < pos := by omega
      rw [hpref _ hlt]
      have e3 : out.size - dist = pos - dist := by omega
      rw [e3, h0]
    simp only [lzCopy]
    rw [hsrc]
    refine ih (pos + 1) (out.push (data.get! pos)) ?_ hd1 (by omega) ?_ ?_ i (by omega)
    · rw [ByteArray.size_push]; omega
    · intro j hj
      rcases Nat.lt_or_ge j pos with hjlt | hjge
      · rw [ByteArray.get!_push_lt out _ j (by omega)]
        exact hpref j hjlt
      · have hjeq : j = pos := by omega
        rw [ByteArray.get!_push_eq out _ j (by omega), hjeq]
    · intro j hj
      have h1 := hmatch (j + 1) (by omega)
      have e1 : pos - dist + (j + 1) = pos + 1 - dist + j := by omega
      have e2 : pos + (j + 1) = pos + 1 + j := by omega
      rw [e1, e2] at h1
      exact h1

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- Token-level L5, the main induction: from any position whose expansion invariant holds,
    the tokenizer's remaining output expands to exactly `data`. Structural induction on the
    tokenizer's fuel; each literal step extends the prefix by one pushed byte, each
    certified match step extends it by `lzCopy_prefix` (L4). -/
theorem tokenizeAux_expand (data : ByteArray) :
    ∀ (fuel pos : Nat) (acc : Array LZToken),
      data.size ≤ pos + fuel → pos ≤ data.size →
      (acc.foldl expandToken ByteArray.empty).size = pos →
      (∀ i, i < pos → (acc.foldl expandToken ByteArray.empty).get! i = data.get! i) →
      (tokenizeAux data fuel pos acc).foldl expandToken ByteArray.empty = data := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos acc hfuel hpos hsz hpref
    simp only [tokenizeAux]
    have hpe : pos = data.size := by omega
    exact ByteArray.ext_get! (by omega) (fun i hi => hpref i (by omega))
  | succ k ih =>
    intro pos acc hfuel hpos hsz hpref
    simp only [tokenizeAux]
    by_cases hlt : pos < data.size
    · rw [if_pos hlt]
      by_cases hv : 3 ≤ (findLongestMatch data pos 32768 128).1 ∧
          matchValid data pos (findLongestMatch data pos 32768 128).1
            (findLongestMatch data pos 32768 128).2 = true
      · rw [if_pos hv]
        obtain ⟨hlen3, hmv⟩ := hv
        obtain ⟨_, _, hd1, _, hdp, hbound, hmatch⟩ := matchValid_spec hmv
        refine ih (pos + (findLongestMatch data pos 32768 128).1) _
          (by omega) (by omega) ?_ ?_
        · rw [Array.foldl_push]
          show (expandToken _ (.ref _ _)).size = _
          simp only [expandToken]
          rw [lzCopy_size, hsz]
        · intro i hi
          rw [Array.foldl_push]
          show (expandToken _ (.ref _ _)).get! i = _
          simp only [expandToken]
          exact lzCopy_prefix data _ _ pos _ hsz hd1 hdp hpref hmatch i hi
      · rw [if_neg hv]
        refine ih (pos + 1) _ (by omega) (by omega) ?_ ?_
        · rw [Array.foldl_push]
          show (expandToken _ (.lit _)).size = _
          simp only [expandToken]
          rw [ByteArray.size_push, hsz]
        · intro i hi
          rw [Array.foldl_push]
          show (expandToken _ (.lit _)).get! i = _
          simp only [expandToken]
          rcases Nat.lt_or_ge i pos with hilt | hige
          · rw [ByteArray.get!_push_lt _ _ i (by omega)]
            exact hpref i hilt
          · have hieq : i = pos := by omega
            rw [ByteArray.get!_push_eq _ _ i (by omega), hieq]
    · rw [if_neg hlt]
      exact ByteArray.ext_get! (by omega) (fun i hi => hpref i (by omega))

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- Universal LZ77 token-layer roundtrip soundness: for EVERY `ByteArray`, the greedy
    tokenizer's output — literals plus certified back-references, including
    self-overlapping RFC 1951 §3.2.3 matches — expands back to exactly the input.
    Kernel-checked structural proof (rung 1); no `native_decide`, no sampling. This is the
    L3+L4+token-level-L5 payload of the PA16 `deflate_roundtrip_soundness` decomposition;
    the Huffman/bitstream layer above it remains blocked on PA16 P0. -/
theorem lz77_roundtrip_soundness (data : ByteArray) :
    expandTokens (tokenize data) = data := by
  unfold expandTokens tokenize
  refine tokenizeAux_expand data data.size 0 #[] (by omega) (by omega) ?_ ?_
  · rfl
  · intro i hi
    omega

/-
## PA16 L1a: bitstream writer ghost algebra (write-append)

The `List Bool` ghost bit-sequence `docs/PA16_CODEC_SOUNDNESS.md` §4 L1 calls for, plus the
write-append law L1a: under the writer's operating invariant (pending bits fit the pending
count, pending count below a byte, no `UInt32` overflow), `writeBits` appends exactly the
`n` LSB-first bits of `v` to the emitted bit sequence — and re-establishes the invariant,
so consecutive `writeBits` calls compose. Kernel-checked structural proofs (rung 1).
-/

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- LSB-first list of the low `n` bits of `v` — the ghost denotation of `n` bits written
    with value `v`. -/
def natBits : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, v => (v % 2 == 1) :: natBits n (v / 2)

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ghost denotation of a finished byte buffer: each byte contributes its 8 bits LSB-first,
    bytes in order — exactly RFC 1951 §3.1.1's bit packing. -/
def bytesBits (bs : ByteArray) : List Bool :=
  bs.data.toList.flatMap fun b => natBits 8 b.toNat

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ghost denotation of a `BitWriter`: all fully emitted bytes followed by the pending
    sub-byte bits. -/
def writerBits (w : BitWriter) : List Bool :=
  bytesBits w.bytes ++ natBits w.bitCount w.bitBuf.toNat

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Splitting law for the ghost bit sequence: the low `m` bits of `a + b·2^m` (with `a`
    fitting in `m` bits) are the bits of `a`, followed by the bits of `b`. -/
theorem natBits_append (n : Nat) : ∀ (m a b : Nat), a < 2 ^ m →
    natBits (m + n) (a + b * 2 ^ m) = natBits m a ++ natBits n b := by
  intro m
  induction m with
  | zero =>
    intro a b ha
    have ha0 : a = 0 := by simp [Nat.pow_zero] at ha; omega
    subst ha0
    simp [natBits]
  | succ m ih =>
    intro a b ha
    have hc : b * 2 ^ (m + 1) = (b * 2 ^ m) * 2 := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [Nat.pow_succ]
    have e : m + 1 + n = (m + n) + 1 := by omega
    rw [e]
    simp only [natBits]
    have hmod : (a + b * 2 ^ (m + 1)) % 2 = a % 2 := by
      rw [hc]; omega
    have hdiv : (a + b * 2 ^ (m + 1)) / 2 = a / 2 + b * 2 ^ m := by
      rw [hc]; omega
    rw [hmod, hdiv, ih (a / 2) b (by rw [hpow] at ha; omega)]
    rfl

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- The writer's `|||`-composition equals plain addition when the pending bits fit below
    the shift — the arithmetic form the ghost algebra computes with. -/
theorem lor_shiftLeft_eq_add {a v m : Nat} (ha : a < 2 ^ m) :
    a ||| v <<< m = a + v * 2 ^ m := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Pushing a byte appends its 8 bits to the buffer's ghost denotation. -/
theorem bytesBits_push (bs : ByteArray) (b : UInt8) :
    bytesBits (bs.push b) = bytesBits bs ++ natBits 8 b.toNat := by
  simp [bytesBits, ByteArray.data_push, Array.toList_push]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `flushBytes` invariant + ghost preservation: draining full bytes out of the pending
    buffer leaves fewer than 8 pending bits, keeps the pending value inside the pending
    count, and preserves the total emitted bit sequence exactly. -/
theorem flushBytes_spec : ∀ (cnt : Nat) (buf : UInt32) (acc : ByteArray),
    buf.toNat < 2 ^ cnt → cnt ≤ 32 →
    (writeBits.flushBytes buf cnt acc).2.1 < 8 ∧
    (writeBits.flushBytes buf cnt acc).1.toNat < 2 ^ (writeBits.flushBytes buf cnt acc).2.1 ∧
    bytesBits (writeBits.flushBytes buf cnt acc).2.2 ++
      natBits (writeBits.flushBytes buf cnt acc).2.1 (writeBits.flushBytes buf cnt acc).1.toNat
      = bytesBits acc ++ natBits cnt buf.toNat := by
  intro cnt
  induction cnt using Nat.strongRecOn with
  | ind cnt ih =>
    intro buf acc hbuf hcnt
    rw [writeBits.flushBytes]
    by_cases h8 : cnt ≥ 8
    · rw [if_pos h8]
      -- the recursive call's arguments
      have h256 : (2 : Nat) ^ 8 = 256 := by decide
      have hbyteNat : ((buf.toNat &&& 0xFF).toUInt8).toNat = buf.toNat % 256 := by
        have hmask : buf.toNat &&& 0xFF = buf.toNat % 256 := by
          have : (0xFF : Nat) = 2 ^ 8 - 1 := by decide
          rw [this, Nat.and_two_pow_sub_one_eq_mod, h256]
        simp [Nat.toUInt8, hmask, UInt8.toNat_ofNat']
      have hnewNat : ((buf.toNat >>> 8).toUInt32).toNat = buf.toNat / 256 := by
        have hshift : buf.toNat >>> 8 = buf.toNat / 256 := by
          rw [Nat.shiftRight_eq_div_pow, h256]
        have hlt : buf.toNat / 256 < 2 ^ 32 := by
          have h32 : (2 : Nat) ^ cnt ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hcnt
          omega
        simp [Nat.toUInt32, hshift, UInt32.toNat_ofNat']
        omega
      have hsplit : 2 ^ cnt = 2 ^ (cnt - 8) * 256 := by
        have : cnt = (cnt - 8) + 8 := by omega
        rw [this, Nat.pow_add, h256]
        have e2 : (cnt - 8) + 8 - 8 = cnt - 8 := by omega
        rw [e2]
      have hrec := ih (cnt - 8) (by omega) ((buf.toNat >>> 8).toUInt32)
        (acc.push (buf.toNat &&& 0xFF).toUInt8)
        (by rw [hnewNat]; rw [hsplit] at hbuf; omega)
        (by omega)
      refine ⟨hrec.1, hrec.2.1, ?_⟩
      rw [hrec.2.2, bytesBits_push, hbyteNat, hnewNat, List.append_assoc]
      congr 1
      have hdecomp : buf.toNat = buf.toNat % 256 + (buf.toNat / 256) * 2 ^ 8 := by
        rw [h256]; omega
      have happ := natBits_append (cnt - 8) 8 (buf.toNat % 256) (buf.toNat / 256)
        (by rw [h256]; omega)
      rw [← hdecomp] at happ
      have ecnt : 8 + (cnt - 8) = cnt := by omega
      rw [ecnt] at happ
      exact happ.symm
    · rw [if_neg h8]
      exact ⟨show cnt < 8 by omega, hbuf, rfl⟩

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- L1a, the write-append law (`docs/PA16_CODEC_SOUNDNESS.md` §4 L1): under the writer's
    operating invariant — pending value inside the pending count, pending count below a
    byte after any previous `writeBits` (`flushBytes_spec`), and no `UInt32` overflow
    (`bitCount + n ≤ 32`; every call site in `compress` writes ≤ 15 bits onto < 8 pending) —
    `writeBits w v n` with `v < 2^n` appends exactly the `n` LSB-first bits of `v` to the
    emitted ghost bit sequence, and re-establishes the invariant so calls compose. -/
theorem writerBits_writeBits (w : BitWriter) (v n : Nat)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount)
    (hv : v < 2 ^ n) (hcnt : w.bitCount + n ≤ 32) :
    writerBits (writeBits w v n) = writerBits w ++ natBits n v ∧
    (writeBits w v n).bitCount < 8 ∧
    (writeBits w v n).bitBuf.toNat < 2 ^ (writeBits w v n).bitCount := by
  unfold writeBits
  have hP1 : (1 : Nat) ≤ 2 ^ w.bitCount := Nat.one_le_two_pow
  have hQ1 : (1 : Nat) ≤ 2 ^ n := Nat.one_le_two_pow
  have hmul : v * 2 ^ w.bitCount ≤ (2 ^ n - 1) * 2 ^ w.bitCount :=
    Nat.mul_le_mul_right _ (by omega)
  have hsub : (2 ^ n - 1) * 2 ^ w.bitCount = 2 ^ n * 2 ^ w.bitCount - 2 ^ w.bitCount := by
    rw [Nat.sub_mul, Nat.one_mul]
  have hPQ : 2 ^ w.bitCount ≤ 2 ^ n * 2 ^ w.bitCount :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hpowadd : 2 ^ (w.bitCount + n) = 2 ^ n * 2 ^ w.bitCount := by
    rw [Nat.pow_add, Nat.mul_comm]
  have hsumlt : w.bitBuf.toNat + v * 2 ^ w.bitCount < 2 ^ (w.bitCount + n) := by
    rw [hpowadd]; omega
  have h32 : (2 : Nat) ^ (w.bitCount + n) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hcnt
  have hlor : w.bitBuf.toNat ||| v <<< w.bitCount =
      w.bitBuf.toNat + v * 2 ^ w.bitCount := lor_shiftLeft_eq_add hbuf
  have hnewNat : ((w.bitBuf.toNat ||| v <<< w.bitCount).toUInt32).toNat =
      w.bitBuf.toNat + v * 2 ^ w.bitCount := by
    simp [Nat.toUInt32, hlor, UInt32.toNat_ofNat']
    omega
  have hfb := flushBytes_spec (w.bitCount + n)
    ((w.bitBuf.toNat ||| v <<< w.bitCount).toUInt32) w.bytes
    (by rw [hnewNat]; exact hsumlt) hcnt
  refine ⟨?_, hfb.1, hfb.2.1⟩
  show bytesBits _ ++ natBits _ _ = _
  rw [hfb.2.2, hnewNat, natBits_append n w.bitCount w.bitBuf.toNat v hbuf,
    writerBits, List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Zero has all-false bits at every width. -/
theorem natBits_zero (n : Nat) : natBits n 0 = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natBits, ih, List.replicate_succ]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Writer half of L1c (`docs/PA16_CODEC_SOUNDNESS.md` §4 L1): byte-aligning flush emits
    exactly the writer's ghost bit sequence followed by sub-byte zero padding — the padding
    RFC 1951 decoding never reads, because it stops at the final block's EOB symbol. -/
theorem flushBitWriter_bits (w : BitWriter)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    bytesBits (flushBitWriter w) =
      writerBits w ++ List.replicate ((8 - w.bitCount) % 8) false := by
  unfold flushBitWriter writerBits
  by_cases h0 : w.bitCount > 0
  · rw [if_pos h0]
    have hsmall : w.bitBuf.toNat < 256 := by
      have : (2 : Nat) ^ w.bitCount ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      have h128 : (2 : Nat) ^ 7 = 128 := by decide
      omega
    have hbyteNat : ((w.bitBuf.toNat &&& 0xFF).toUInt8).toNat = w.bitBuf.toNat := by
      have hmask : w.bitBuf.toNat &&& 0xFF = w.bitBuf.toNat % 256 := by
        have : (0xFF : Nat) = 2 ^ 8 - 1 := by decide
        have h256 : (2 : Nat) ^ 8 = 256 := by decide
        rw [this, Nat.and_two_pow_sub_one_eq_mod, h256]
      simp [Nat.toUInt8, hmask, UInt8.toNat_ofNat']
      omega
    rw [bytesBits_push, hbyteNat]
    have happ := natBits_append (8 - w.bitCount) w.bitCount w.bitBuf.toNat 0 hbuf
    have e1 : w.bitBuf.toNat + 0 * 2 ^ w.bitCount = w.bitBuf.toNat := by omega
    have e2 : w.bitCount + (8 - w.bitCount) = 8 := by omega
    rw [e1, e2, natBits_zero] at happ
    have e3 : (8 - w.bitCount) % 8 = 8 - w.bitCount := by omega
    rw [happ, e3, List.append_assoc]
  · rw [if_neg h0]
    have e0 : w.bitCount = 0 := by omega
    simp [e0, natBits]

/-
## PA16 L1b: bitstream reader ghost algebra (read-consume)

Read-side dual of L1a above, unblocked by P0's conversion of `ensureBits` to well-founded
recursion. `readerBits` is the ghost sequence of unconsumed bits; `ensureBits` preserves it
(buffering moves bits, never consumes them), and a successful `readBits r n` returns exactly
the value whose LSB-first bits are the first `n` elements of the sequence, leaving the rest —
with the reader's operating invariant re-established so reads compose. All rung-1.
-/

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ghost denotation of a `BitReader`: the unconsumed bit sequence — buffered bits first
    (LSB-first), then the bits of every unread byte in stream order. -/
def readerBits (r : BitReader) : List Bool :=
  natBits r.bitCount r.bitBuf.toNat ++
    (r.bytes.data.toList.drop r.bytePos).flatMap fun b => natBits 8 b.toNat

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Every `natBits` window has exactly its stated width. -/
theorem natBits_length (n : Nat) : ∀ v, (natBits n v).length = n := by
  induction n with
  | zero => intro v; rfl
  | succ n ih => intro v; simp [natBits, ih]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- A value below `2^n` is recovered exactly from its `n`-bit LSB-first window — the
    injectivity half of the ghost encoding, used to transport a written value across the
    writer→reader correspondence. -/
theorem bitsVal_natBits_of_lt : ∀ (n v : Nat), v < 2 ^ n →
    (natBits n v).foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0 = v := by
  intro n
  induction n with
  | zero =>
    intro v hv
    simp [Nat.pow_zero] at hv
    simp [natBits, hv]
  | succ n ih =>
    intro v hv
    have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
    simp only [natBits, List.foldr_cons]
    rw [ih (v / 2) (by rw [hpow] at hv; omega)]
    have hb : (if (v % 2 == 1) = true then 1 else 0) = v % 2 := by
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    rw [hb]
    omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `natBits` windows are injective below `2^n`. -/
theorem natBits_inj {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : natBits n a = natBits n b) : a = b := by
  have h1 := bitsVal_natBits_of_lt n a ha
  have h2 := bitsVal_natBits_of_lt n b hb
  rw [← h1, ← h2, h]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Splits any bit window at position `m`: low `m` bits of the residue, then the shifted
    remainder. `natBits_append` specialized through Euclidean decomposition. -/
theorem natBits_split (m n v : Nat) :
    natBits (m + n) v = natBits m (v % 2 ^ m) ++ natBits n (v / 2 ^ m) := by
  have hdec : v = v % 2 ^ m + (v / 2 ^ m) * 2 ^ m := (Nat.mod_add_div' v (2 ^ m)).symm
  conv => lhs; rw [hdec]
  exact natBits_append n m (v % 2 ^ m) (v / 2 ^ m) (Nat.mod_lt v (Nat.two_pow_pos m))

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Disjoint-sum bound: a value below `2^m` plus a `k`-bit value shifted by `m` stays below
    `2^(m+k)` — the no-`UInt32`-overflow fact both bitstream directions rely on. -/
theorem add_mul_pow_lt {a v m k : Nat} (ha : a < 2 ^ m) (hv : v < 2 ^ k) :
    a + v * 2 ^ m < 2 ^ (m + k) := by
  have h1 : v * 2 ^ m ≤ (2 ^ k - 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 ^ k - 1) * 2 ^ m = 2 ^ k * 2 ^ m - 1 * 2 ^ m := by rw [Nat.sub_mul]
  have h3 : 2 ^ m ≤ 2 ^ k * 2 ^ m := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
  have h4 : 2 ^ (m + k) = 2 ^ k * 2 ^ m := by rw [Nat.pow_add, Nat.mul_comm]
  rw [h4]
  omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- The reader/writer `UInt32` buffer composition in `Nat` terms: given the operating
    invariant and no 32-bit overflow, `buf ||| v <<< cnt` round-trips through `UInt32`
    as the exact sum `buf + v * 2^cnt`. -/
theorem buf_or_shift_toNat {buf v cnt k : Nat} (hbuf : buf < 2 ^ cnt) (hv : v < 2 ^ k)
    (h32 : cnt + k ≤ 32) : ((buf ||| v <<< cnt).toUInt32).toNat = buf + v * 2 ^ cnt := by
  have hlor : buf ||| v <<< cnt = buf + v * 2 ^ cnt := lor_shiftLeft_eq_add hbuf
  have hlt : buf + v * 2 ^ cnt < 2 ^ 32 := by
    have h1 := add_mul_pow_lt hbuf hv
    have h2 : (2 : Nat) ^ (cnt + k) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) h32
    omega
  simp [Nat.toUInt32, hlor, UInt32.toNat_ofNat']
  omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `ensureBits.loop` ghost preservation + invariant maintenance: buffering never changes
    the unconsumed bit sequence, keeps the buffered value inside the buffered count, keeps
    the buffered count below `n + 8`, leaves the byte source untouched, and stops only with
    `n` bits buffered or the source exhausted. Requires `n ≤ 24` (RFC-1951-side truth: the
    largest single read is 13 extra bits; the buffer is 32 bits wide). -/
theorem ensureBits_loop_spec (n : Nat) (hn : n ≤ 24) (cur : BitReader) :
    cur.bitBuf.toNat < 2 ^ cur.bitCount → cur.bitCount < n + 8 →
    readerBits (ensureBits.loop n cur) = readerBits cur ∧
    (ensureBits.loop n cur).bitBuf.toNat < 2 ^ (ensureBits.loop n cur).bitCount ∧
    (ensureBits.loop n cur).bitCount < n + 8 ∧
    (ensureBits.loop n cur).bytes = cur.bytes ∧
    ((ensureBits.loop n cur).bitCount ≥ n ∨
      (ensureBits.loop n cur).bytePos ≥ (ensureBits.loop n cur).bytes.size) := by
  induction cur using ensureBits.loop.induct (n := n) with
  | case1 x hx =>
    intro hinv hcnt
    rw [ensureBits.loop.eq_1, if_pos hx]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
    exact ⟨rfl, hinv, hcnt, rfl, hx⟩
  | case2 x hx nextByte newBuf ih =>
    intro hinv hcnt
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hx
    have hxc : x.bitCount < n := by omega
    have hxp : x.bytePos < x.bytes.size := by omega
    have hbyte : nextByte.toNat < 2 ^ 8 := UInt8.toNat_lt nextByte
    have hnewNat : newBuf.toNat = x.bitBuf.toNat + nextByte.toNat * 2 ^ x.bitCount :=
      buf_or_shift_toNat hinv hbyte (by omega)
    have hinv' : newBuf.toNat < 2 ^ (x.bitCount + 8) := by
      rw [hnewNat]; exact add_mul_pow_lt hinv hbyte
    have ih' := ih hinv' (by show x.bitCount + 8 < n + 8; omega)
    rw [ensureBits.loop.eq_1, if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]; omega)]
    refine ⟨?_, ih'.2.1, ih'.2.2.1, ih'.2.2.2.1, ?_⟩
    · rw [ih'.1]
      -- readerBits of the buffered-one-more-byte state equals readerBits x
      show natBits (x.bitCount + 8) newBuf.toNat ++
          (x.bytes.data.toList.drop (x.bytePos + 1)).flatMap (fun b => natBits 8 b.toNat) =
        natBits x.bitCount x.bitBuf.toNat ++
          (x.bytes.data.toList.drop x.bytePos).flatMap (fun b => natBits 8 b.toNat)
      have hlen : x.bytePos < x.bytes.data.toList.length := by
        rw [Array.length_toList]
        exact hxp
      have hdrop : x.bytes.data.toList.drop x.bytePos =
          x.bytes.data.toList[x.bytePos] :: x.bytes.data.toList.drop (x.bytePos + 1) :=
        List.drop_eq_getElem_cons hlen
      have hgetEq : x.bytes.data.toList[x.bytePos]'hlen = nextByte := by
        show x.bytes.data.toList[x.bytePos]'hlen = x.bytes.get! x.bytePos
        rw [ByteArray.get!_eq_getElem x.bytes x.bytePos hxp]
        rw [Array.getElem_toList]
        exact ByteArray.getElem_eq_getElem_data.symm
      rw [hdrop, hgetEq, List.flatMap_cons, hnewNat,
        natBits_append 8 x.bitCount x.bitBuf.toNat nextByte.toNat hinv,
        List.append_assoc]
    · rcases ih'.2.2.2.2 with h | h
      · exact Or.inl h
      · exact Or.inr h

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- L1b, the read-consume law (`docs/PA16_CODEC_SOUNDNESS.md` §4 L1): under the reader's
    operating invariant (buffered value inside the buffered count, fewer than 8 buffered
    bits — `mkBitReader`'s initial state, re-established by every successful read) and the
    format-honest width bound `n ≤ 24`, a reader holding at least `n` unconsumed bits
    successfully reads a value `v < 2^n` whose LSB-first window is exactly the first `n`
    ghost bits, leaving exactly the remaining ghost bits — with the invariant restored. -/
theorem readBits_spec (r : BitReader) (n : Nat)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8)
    (hn : n ≤ 24) (hlen : n ≤ (readerBits r).length) :
    ∃ r' v, readBits r n = .ok (r', v) ∧
      v < 2 ^ n ∧
      natBits n v = (readerBits r).take n ∧
      readerBits r' = (readerBits r).drop n ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  have hens : ensureBits r n = ensureBits.loop n r := ensureBits.eq_1 r n
  obtain ⟨hbits, einv, ecnt, ebytes, hexit⟩ := ensureBits_loop_spec n hn r hinv (by omega)
  rw [← hens] at hbits einv ecnt ebytes hexit
  -- the ensured reader holds at least n buffered bits
  have hbcnt : n ≤ (ensureBits r n).bitCount := by
    rcases hexit with h | h
    · exact h
    · have hdropnil :
          (ensureBits r n).bytes.data.toList.drop (ensureBits r n).bytePos = [] := by
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]
        exact h
      have : (readerBits (ensureBits r n)).length = (ensureBits r n).bitCount := by
        simp [readerBits, hdropnil, natBits_length]
      rw [hbits] at this
      omega
  have hdivNat : (((ensureBits r n).bitBuf.toNat >>> n).toUInt32).toNat =
      (ensureBits r n).bitBuf.toNat / 2 ^ n := by
    have hshift : (ensureBits r n).bitBuf.toNat >>> n = (ensureBits r n).bitBuf.toNat / 2 ^ n :=
      Nat.shiftRight_eq_div_pow _ n
    have hlt : (ensureBits r n).bitBuf.toNat / 2 ^ n < 2 ^ 32 := by
      have h1 : (2 : Nat) ^ (ensureBits r n).bitCount ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (ensureBits r n).bitBuf.toNat / 2 ^ n ≤ (ensureBits r n).bitBuf.toNat :=
        Nat.div_le_self _ _
      omega
    simp [Nat.toUInt32, hshift, UInt32.toNat_ofNat']
    omega
  have hsplit := natBits_split n ((ensureBits r n).bitCount - n) (ensureBits r n).bitBuf.toNat
  rw [show n + ((ensureBits r n).bitCount - n) = (ensureBits r n).bitCount by omega] at hsplit
  have hread : readBits r n =
      .ok ({ ensureBits r n with
              bitBuf := ((ensureBits r n).bitBuf.toNat >>> n).toUInt32,
              bitCount := (ensureBits r n).bitCount - n },
        (ensureBits r n).bitBuf.toNat &&& ((1 <<< n) - 1)) := by
    simp only [readBits]
    rw [if_neg (by omega)]
  refine ⟨_, _, hread, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- value bound
    have h1n : (1 : Nat) <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [h1n, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos n)
  · -- the value's window is the ghost prefix
    have h1n : (1 : Nat) <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [h1n, Nat.and_two_pow_sub_one_eq_mod, ← hbits]
    show natBits n ((ensureBits r n).bitBuf.toNat % 2 ^ n) = (readerBits (ensureBits r n)).take n
    rw [readerBits, hsplit, List.append_assoc]
    rw [List.take_left' (by rw [natBits_length])]
  · -- the rest is the ghost suffix
    rw [← hbits]
    show natBits ((ensureBits r n).bitCount - n)
        (((ensureBits r n).bitBuf.toNat >>> n).toUInt32).toNat ++ _ =
      (readerBits (ensureBits r n)).drop n
    rw [hdivNat, readerBits, hsplit, List.append_assoc]
    rw [List.drop_left' (by rw [natBits_length])]
  · -- invariant: new buffered value inside new count
    show (((ensureBits r n).bitBuf.toNat >>> n).toUInt32).toNat <
      2 ^ ((ensureBits r n).bitCount - n)
    rw [hdivNat]
    have hdecomp : (2 : Nat) ^ (ensureBits r n).bitCount =
        2 ^ ((ensureBits r n).bitCount - n) * 2 ^ n := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
    rw [hdecomp] at einv
    exact einv
  · -- invariant: new count below 8
    show (ensureBits r n).bitCount - n < 8
    omega
  · -- bytes untouched
    show (ensureBits r n).bytes = r.bytes
    exact ebytes

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `mkBitReader`'s ghost sequence is the byte buffer's bit sequence, and its operating
    invariant holds initially. -/
theorem readerBits_mkBitReader (bs : ByteArray) :
    readerBits (mkBitReader bs) = bytesBits bs ∧
    (mkBitReader bs).bitBuf.toNat < 2 ^ (mkBitReader bs).bitCount ∧
    (mkBitReader bs).bitCount < 8 := by
  refine ⟨?_, by simp [mkBitReader], by simp [mkBitReader]⟩
  simp [readerBits, mkBitReader, bytesBits, natBits]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- L1c, the writer↔reader correspondence: a reader over a flushed writer's bytes sees
    exactly the writer's ghost bit sequence followed by the byte-alignment zero padding —
    the composition point where L1a's write-append meets L1b's read-consume. -/
theorem readerBits_of_flushed (w : BitWriter)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    readerBits (mkBitReader (flushBitWriter w)) =
      writerBits w ++ List.replicate ((8 - w.bitCount) % 8) false := by
  rw [(readerBits_mkBitReader (flushBitWriter w)).1]
  exact flushBitWriter_bits w hbuf hcnt

/-
## PA16 L2 groundwork: Huffman decode-tree path semantics

`treeWalk` is the computable ghost semantics of a decode tree: follow a bit path from a
node to a leaf. `decodeHuffmanSymbol_spec` proves the general decode law — for ANY table
(fixed or dynamic): if some path through the tree reaches leaf `sym` and the reader's
unconsumed ghost bits start with that path, decoding succeeds with `sym`, consumes exactly
the path, and re-establishes the reader invariant. Per-table facts (which path each
symbol's canonical code takes) then plug in as closed hypotheses.
-/

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Follows a bit path from a decode-tree node; `some sym` iff the path ends exactly on a
    leaf carrying `sym`. -/
def treeWalk : HuffmanNode → List Bool → Option Nat
  | .leaf sym, [] => some sym
  | .branch l _, false :: p =>
    match l with
    | some n => treeWalk n p
    | none => none
  | .branch _ rr, true :: p =>
    match rr with
    | some n => treeWalk n p
    | none => none
  | _, _ => none

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- General Huffman decode law over the tree-path semantics: from any tree node, if the
    reader's ghost bits start with a path that `treeWalk` resolves to `sym`, then
    `decodeHuffmanSymbol.step` succeeds with `sym`, consumes exactly the path, keeps the
    byte source, and re-establishes the reader's operating invariant. -/
theorem decodeHuffmanSymbol_step_spec (path : List Bool) :
    ∀ (node : HuffmanNode) (sym : Nat) (r : BitReader) (rest : List Bool),
      treeWalk node path = some sym →
      readerBits r = path ++ rest →
      r.bitBuf.toNat < 2 ^ r.bitCount → r.bitCount < 8 →
      ∃ r', decodeHuffmanSymbol.step r node = .ok (r', sym) ∧
        readerBits r' = rest ∧
        r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  induction path with
  | nil =>
    intro node sym r rest hwalk hbits hinv hcnt
    match node with
    | .leaf s =>
      simp only [treeWalk, Option.some.injEq] at hwalk
      subst hwalk
      refine ⟨r, ?_, by simpa using hbits, hinv, hcnt, rfl⟩
      rw [decodeHuffmanSymbol.step.eq_def]
    | .branch _ _ => simp [treeWalk] at hwalk
  | cons b p ih =>
    intro node sym r rest hwalk hbits hinv hcnt
    match node with
    | .leaf s => simp [treeWalk] at hwalk
    | .branch l rr =>
      -- one bit is available: readerBits r = b :: (p ++ rest)
      have hlen : 1 ≤ (readerBits r).length := by
        rw [hbits]; simp
      obtain ⟨r1, v, hok, hv, hwin, hdrop, hinv1, hcnt1, hbytes1⟩ :=
        readBits_spec r 1 hinv hcnt (by omega) hlen
      -- the single-bit window determines v from b
      have hwin1 : natBits 1 v = [b] := by
        rw [hwin, hbits]
        rfl
      have hmod : (v % 2 == 1) = b := by
        simpa [natBits] using hwin1
      have hv2 : v < 2 := by
        simpa using hv
      have hdrop' : readerBits r1 = p ++ rest := by
        rw [hdrop, hbits]
        rfl
      rw [decodeHuffmanSymbol.step.eq_def]
      simp only [hok]
      rcases b with _ | _
      · -- b = false: v = 0, go left
        have hv0 : v = 0 := by
          have h' : ¬ v % 2 = 1 := by simpa using hmod
          omega
        subst hv0
        cases l with
        | some nl =>
          simp only [treeWalk] at hwalk
          obtain ⟨r', hstep, hbits', hinv', hcnt', hbytes'⟩ :=
            ih nl sym r1 rest hwalk hdrop' hinv1 hcnt1
          refine ⟨r', ?_, hbits', hinv', hcnt', by rw [hbytes', hbytes1]⟩
          simpa using hstep
        | none => simp [treeWalk] at hwalk
      · -- b = true: v = 1, go right
        have hv1 : v = 1 := by
          have h' : v % 2 = 1 := by simpa using hmod
          omega
        subst hv1
        cases rr with
        | some nr =>
          simp only [treeWalk] at hwalk
          obtain ⟨r', hstep, hbits', hinv', hcnt', hbytes'⟩ :=
            ih nr sym r1 rest hwalk hdrop' hinv1 hcnt1
          refine ⟨r', ?_, hbits', hinv', hcnt', by rw [hbytes', hbytes1]⟩
          simpa using hstep
        | none => simp [treeWalk] at hwalk

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Top-level form of the decode law, phrased over `decodeHuffmanSymbol` and a table. -/
theorem decodeHuffmanSymbol_spec (table : HuffmanTable) (path : List Bool) (sym : Nat)
    (r : BitReader) (rest : List Bool)
    (hwalk : treeWalk table.root path = some sym)
    (hbits : readerBits r = path ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r table = .ok (r', sym) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  rw [decodeHuffmanSymbol]
  exact decodeHuffmanSymbol_step_spec path table.root sym r rest hwalk hbits hinv hcnt

/-
## PA16 L2-fixed: the two closed RFC 1951 §3.2.6 tables invert their own codes

The general decode law (`decodeHuffmanSymbol_spec`) needs, per table, the closed fact that
each symbol's emitted bit path (`emitHuffSymbol` writes `reverseBits code len` LSB-first,
i.e. the canonical code MSB-first per RFC 1951 §3.1.1) walks the decode tree back to that
same symbol. For the two fixed tables this is a finite, closed proposition: 288 + 32
symbols of a compile-time constant construction. `decide` cannot evaluate the `Id.run`/
`for` loops directly (`Std.Range.forIn'.loop` is well-founded recursion, opaque to kernel
reduction), so each check first normalizes the loops to `List.foldl` with the same
`Std.Legacy.Range` simp set `encode_distance_bounds_inst` already uses, then decides the
resulting structural computation.
-/

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Ghost bit path emitted for `sym` by `emitHuffSymbol` under `table`: the canonical code
    bit-reversed for LSB-first packing, as a `List Bool` window. Empty for absent symbols
    (`emitHuffSymbol` likewise emits nothing). -/
def symbolBits (t : HuffmanTable) (sym : Nat) : List Bool :=
  match t.codes[sym]! with
  | some (code, len) => natBits len (reverseBits code len)
  | none => []

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- `symbolBits` unfolding for a present symbol. -/
theorem symbolBits_eq (t : HuffmanTable) (sym code len : Nat)
    (hc : t.codes[sym]! = some (code, len)) :
    symbolBits t sym = natBits len (reverseBits code len) := by
  unfold symbolBits
  rw [hc]

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- The per-symbol Bool check whose `decide`-closure certifies one table: every symbol
    below `n` has a code of positive length ≤ 9 whose bit-reversal fits its width and
    whose emitted path decodes back to the symbol. -/
def tableCheck (t : HuffmanTable) (n : Nat) : Bool :=
  (List.range n).all fun sym =>
    match t.codes[sym]! with
    | some (code, len) =>
      decide (0 < len) && decide (len ≤ 9) && decide (reverseBits code len < 2 ^ len) &&
        (treeWalk t.root (natBits len (reverseBits code len)) == some sym)
    | none => false

set_option maxRecDepth 40000 in
/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Closed check of the 288-symbol RFC 1951 §3.2.6 fixed literal/length table. -/
theorem fixedLit_check : tableCheck fixedLitLenTable 288 = true := by
  simp only [tableCheck, fixedLitLenTable, fixedLitLenLengths, buildHuffmanTable,
    reverseBits, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  decide

set_option maxRecDepth 20000 in
/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Closed check of the 32-symbol RFC 1951 §3.2.6 fixed distance table. -/
theorem fixedDist_check : tableCheck fixedDistTable 32 = true := by
  simp only [tableCheck, fixedDistTable, fixedDistLengths, buildHuffmanTable,
    reverseBits, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  decide

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Extraction of a passed `tableCheck` into per-symbol propositional facts. -/
theorem tableCheck_spec {t : HuffmanTable} {n : Nat} (hcheck : tableCheck t n = true)
    {sym : Nat} (hsym : sym < n) :
    ∃ code len, t.codes[sym]! = some (code, len) ∧ 0 < len ∧ len ≤ 9 ∧
      reverseBits code len < 2 ^ len ∧
      treeWalk t.root (natBits len (reverseBits code len)) = some sym := by
  have h := List.all_eq_true.mp hcheck sym (List.mem_range.mpr hsym)
  revert h
  cases hc : t.codes[sym]! with
  | none => intro h; simp at h
  | some cl =>
    obtain ⟨code, len⟩ := cl
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨code, len, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- L2-fixed, literal/length side: every fixed literal/length symbol's emitted path
    decodes back to it, with the emission-side bounds needed by `writerBits_writeBits`. -/
theorem fixedLit_symbol_spec {sym : Nat} (hsym : sym < 288) :
    ∃ code len, fixedLitLenTable.codes[sym]! = some (code, len) ∧ 0 < len ∧ len ≤ 9 ∧
      reverseBits code len < 2 ^ len ∧
      treeWalk fixedLitLenTable.root (natBits len (reverseBits code len)) = some sym :=
  tableCheck_spec fixedLit_check hsym

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- L2-fixed, distance side. -/
theorem fixedDist_symbol_spec {sym : Nat} (hsym : sym < 32) :
    ∃ code len, fixedDistTable.codes[sym]! = some (code, len) ∧ 0 < len ∧ len ≤ 9 ∧
      reverseBits code len < 2 ^ len ∧
      treeWalk fixedDistTable.root (natBits len (reverseBits code len)) = some sym :=
  tableCheck_spec fixedDist_check hsym

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- L2-fixed decode form, literal/length side: a reader whose ghost bits start with a
    fixed literal/length symbol's emitted path decodes exactly that symbol, consumes
    exactly the path, and re-establishes the reader invariant. -/
theorem decodeHuffmanSymbol_fixedLit {sym : Nat} (hsym : sym < 288) (r : BitReader)
    (rest : List Bool) (hbits : readerBits r = symbolBits fixedLitLenTable sym ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r fixedLitLenTable = .ok (r', sym) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  obtain ⟨code, len, hc, _, _, _, hwalk⟩ := fixedLit_symbol_spec hsym
  rw [symbolBits_eq _ _ _ _ hc] at hbits
  exact decodeHuffmanSymbol_spec _ _ _ _ _ hwalk hbits hinv hcnt

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- L2-fixed decode form, distance side. -/
theorem decodeHuffmanSymbol_fixedDist {sym : Nat} (hsym : sym < 32) (r : BitReader)
    (rest : List Bool) (hbits : readerBits r = symbolBits fixedDistTable sym ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r fixedDistTable = .ok (r', sym) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  obtain ⟨code, len, hc, _, _, _, hwalk⟩ := fixedDist_symbol_spec hsym
  rw [symbolBits_eq _ _ _ _ hc] at hbits
  exact decodeHuffmanSymbol_spec _ _ _ _ _ hwalk hbits hinv hcnt

/-
## PA16 L6-adjacent: length/distance code algebra shared by encoder and decoder
-/

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- One-level `ite` peeling under an arbitrary explicit motive — the general-motive form
    of `ite_fst_le`, for conjunction goals over a nested threshold-band `if` chain. -/
theorem ite_spec {c : Prop} [Decidable c] {α : Sort _} {P : α → Prop} (a b : α)
    (ha : c → P a) (hb : ¬c → P b) : P (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- `encodeLength` agrees with the decoder's `lengthTable` on every valid match length:
    the symbol lands in `[257, 285]`, the extra-bits value fits its width, and base plus
    extra reconstructs the length exactly. Closed 256-case check (RFC 1951 §3.2.5). -/
theorem encodeLength_spec :
    ∀ len : Nat, len < 259 → 3 ≤ len →
      257 ≤ (encodeLength len).1 ∧ (encodeLength len).1 ≤ 285 ∧
      (encodeLength len).2.1 ≤ 5 ∧
      (encodeLength len).2.2 < 2 ^ (encodeLength len).2.1 ∧
      lengthTable[(encodeLength len).1 - 257]!.1 + (encodeLength len).2.2 = len ∧
      lengthTable[(encodeLength len).1 - 257]!.2 = (encodeLength len).2.1 := by
  decide

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- The `encodeDistance` consistency predicate, named so `ite_spec`'s motive is explicit
    (higher-order motive inference misresolves on the 27-band nested `ite` chain). -/
def EDP (dist : Nat) (t : Nat × Nat × Nat) : Prop :=
  t.1 ≤ 29 ∧ t.2.1 ≤ 13 ∧ t.2.2 < 2 ^ t.2.1 ∧
  distanceTable[t.1]!.1 + t.2.2 = dist ∧ distanceTable[t.1]!.2 = t.2.1

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- `encodeDistance` agrees with the decoder's `distanceTable` on every valid distance:
    the code is ≤ 29 (so the decoder's `distSym ≥ 30` guard passes), the extra-bits value
    fits its width (≤ 13 bits), and base plus extra reconstructs the distance exactly.
    Proven structurally by band-peeling (RFC 1951 §3.2.5's 30 distance bands), not by
    enumerating the 32768 distances — `decide` at that scale exceeds the kernel budget
    (see `encode_distance_bounds_inst`). -/
theorem encodeDistance_spec (dist : Nat) (h1 : 1 ≤ dist) (h2 : dist ≤ 32768) :
    EDP dist (encodeDistance dist) := by
  unfold encodeDistance
  repeat' (apply ite_spec (P := EDP dist) <;> intro h)
  all_goals
    first
    | (simp [EDP, distanceTable]; omega)
    | (have hd : dist = 1 ∨ dist = 2 ∨ dist = 3 ∨ dist = 4 := by omega
       rcases hd with rfl | rfl | rfl | rfl <;> simp [EDP, distanceTable])

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- `encodeDistance_spec` with the conjunction unfolded (same proposition, `EDP` is
    definitionally transparent). -/
theorem encodeDistance_spec' (dist : Nat) (h1 : 1 ≤ dist) (h2 : dist ≤ 32768) :
    (encodeDistance dist).1 ≤ 29 ∧ (encodeDistance dist).2.1 ≤ 13 ∧
    (encodeDistance dist).2.2 < 2 ^ (encodeDistance dist).2.1 ∧
    distanceTable[(encodeDistance dist).1]!.1 + (encodeDistance dist).2.2 = dist ∧
    distanceTable[(encodeDistance dist).1]!.2 = (encodeDistance dist).2.1 :=
  encodeDistance_spec dist h1 h2

/-
## PA16 L5-writer (fixed path): the emitted ghost bit sequence of a fixed-Huffman block

Everything below is about the *writer* half of the fixed-block roundtrip: `emitFixedBlock`
emits exactly `BFINAL=1, BTYPE=01` followed by each token's Huffman code + extra bits and
the end-of-block symbol, as a ghost `List Bool`. The reader half (that `decompress`
consumes exactly these bits back into the original tokens) additionally needs
`decodeHuffmanStream`/`decompress` converted off `partial` and is assembled separately.
-/

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- RFC 1951 range validity of one LZ77 token — exactly the ranges `matchValid` certifies
    for back-references; literals are unconditionally valid. -/
def tokenRangesOk : LZToken → Prop
  | .lit _ => True
  | .ref len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bit sequence one token contributes under the fixed tables: length/literal code,
    length extra bits, then (for refs) distance code and distance extra bits. -/
def tokenBitsFixed : LZToken → List Bool
  | .lit b => symbolBits fixedLitLenTable b.toNat
  | .ref len dist =>
    symbolBits fixedLitLenTable (encodeLength len).1 ++
    natBits (encodeLength len).2.1 (encodeLength len).2.2 ++
    symbolBits fixedDistTable (encodeDistance dist).1 ++
    natBits (encodeDistance dist).2.1 (encodeDistance dist).2.2

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bit sequence of a token list under the fixed tables. -/
def tokensBitsFixed : List LZToken → List Bool
  | [] => []
  | t :: ts => tokenBitsFixed t ++ tokensBitsFixed ts

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emitting one coded symbol appends its ghost path and preserves the writer invariant. -/
theorem writerBits_emitHuffSymbol (w : BitWriter) (t : HuffmanTable) (sym code len : Nat)
    (hc : t.codes[sym]! = some (code, len)) (hlen : len ≤ 24)
    (hval : reverseBits code len < 2 ^ len)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    writerBits (emitHuffSymbol w t sym) = writerBits w ++ symbolBits t sym ∧
    (emitHuffSymbol w t sym).bitCount < 8 ∧
    (emitHuffSymbol w t sym).bitBuf.toNat < 2 ^ (emitHuffSymbol w t sym).bitCount := by
  unfold emitHuffSymbol
  rw [hc, symbolBits_eq t sym code len hc]
  exact writerBits_writeBits w _ len hbuf hval (by omega)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Conditional extra-bits write: appends exactly `natBits n v` whether or not `n = 0`
    (`natBits 0 v = []`, and the encoder skips the zero-width write). -/
theorem writerBits_writeExtra (w : BitWriter) (v n : Nat)
    (hv : v < 2 ^ n) (hn : n ≤ 24)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    writerBits (if n > 0 then writeBits w v n else w) = writerBits w ++ natBits n v ∧
    (if n > 0 then writeBits w v n else w).bitCount < 8 ∧
    (if n > 0 then writeBits w v n else w).bitBuf.toNat <
      2 ^ (if n > 0 then writeBits w v n else w).bitCount := by
  split
  · exact writerBits_writeBits w v n hbuf hv (by omega)
  · rename_i hn0
    have h0 : n = 0 := by omega
    subst h0
    exact ⟨by simp [natBits], hcnt, hbuf⟩

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emitting one range-valid token under the fixed tables appends its ghost bits and
    preserves the writer invariant. -/
theorem writerBits_emitToken_fixed (w : BitWriter) (t : LZToken) (hok : tokenRangesOk t)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    writerBits (emitToken fixedLitLenTable fixedDistTable w t) =
      writerBits w ++ tokenBitsFixed t ∧
    (emitToken fixedLitLenTable fixedDistTable w t).bitCount < 8 ∧
    (emitToken fixedLitLenTable fixedDistTable w t).bitBuf.toNat <
      2 ^ (emitToken fixedLitLenTable fixedDistTable w t).bitCount := by
  cases t with
  | lit b =>
    obtain ⟨code, len, hc, _, hlen9, hval, _⟩ :=
      fixedLit_symbol_spec (sym := b.toNat) (by have := b.toNat_lt; omega)
    have h := writerBits_emitHuffSymbol w fixedLitLenTable b.toNat code len hc
      (by omega) hval hbuf hcnt
    exact ⟨h.1, h.2.1, h.2.2⟩
  | ref len dist =>
    obtain ⟨h3, h258, h1d, hd32768⟩ := hok
    have hL := encodeLength_spec len (by omega) h3
    have hD := encodeDistance_spec' dist h1d hd32768
    obtain ⟨hL257, hL285, hLeb, hLev, _, _⟩ := hL
    obtain ⟨hDc, hDeb, hDev, _, _⟩ := hD
    obtain ⟨lc, ll, hlc, _, hll9, hlval, _⟩ :=
      fixedLit_symbol_spec (sym := (encodeLength len).1) (by omega)
    have s1 := writerBits_emitHuffSymbol w fixedLitLenTable (encodeLength len).1 lc ll hlc
      (by omega) hlval hbuf hcnt
    have s2 := writerBits_writeExtra (emitHuffSymbol w fixedLitLenTable (encodeLength len).1)
      (encodeLength len).2.2 (encodeLength len).2.1 hLev (by omega) s1.2.2 s1.2.1
    obtain ⟨dc, dl, hdc, _, hdl9, hdval, _⟩ :=
      fixedDist_symbol_spec (sym := (encodeDistance dist).1) (by omega)
    have s3 := writerBits_emitHuffSymbol _ fixedDistTable (encodeDistance dist).1 dc dl hdc
      (by omega) hdval s2.2.2 s2.2.1
    have s4 := writerBits_writeExtra _ (encodeDistance dist).2.2 (encodeDistance dist).2.1
      hDev (by omega) s3.2.2 s3.2.1
    refine ⟨?_, s4.2.1, s4.2.2⟩
    show writerBits _ = _
    rw [show emitToken fixedLitLenTable fixedDistTable w (.ref len dist) =
      (if (encodeDistance dist).2.1 > 0 then
        writeBits
          (emitHuffSymbol
            (if (encodeLength len).2.1 > 0 then
              writeBits (emitHuffSymbol w fixedLitLenTable (encodeLength len).1)
                (encodeLength len).2.2 (encodeLength len).2.1
             else emitHuffSymbol w fixedLitLenTable (encodeLength len).1)
            fixedDistTable (encodeDistance dist).1)
          (encodeDistance dist).2.2 (encodeDistance dist).2.1
       else
        emitHuffSymbol
          (if (encodeLength len).2.1 > 0 then
            writeBits (emitHuffSymbol w fixedLitLenTable (encodeLength len).1)
              (encodeLength len).2.2 (encodeLength len).2.1
           else emitHuffSymbol w fixedLitLenTable (encodeLength len).1)
          fixedDistTable (encodeDistance dist).1) from rfl]
    rw [s4.1, s3.1, s2.1, s1.1, tokenBitsFixed]
    simp [List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Folding `emitToken` over a range-valid token list appends the concatenated ghost
    bits and preserves the writer invariant. -/
theorem writerBits_foldl_emitToken_fixed (ts : List LZToken) (w : BitWriter)
    (hok : ∀ t ∈ ts, tokenRangesOk t)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    writerBits (ts.foldl (emitToken fixedLitLenTable fixedDistTable) w) =
      writerBits w ++ tokensBitsFixed ts ∧
    (ts.foldl (emitToken fixedLitLenTable fixedDistTable) w).bitCount < 8 ∧
    (ts.foldl (emitToken fixedLitLenTable fixedDistTable) w).bitBuf.toNat <
      2 ^ (ts.foldl (emitToken fixedLitLenTable fixedDistTable) w).bitCount := by
  induction ts generalizing w with
  | nil => exact ⟨by simp [tokensBitsFixed], hcnt, hbuf⟩
  | cons t ts ih =>
    have ht := writerBits_emitToken_fixed w t (hok t (by simp)) hbuf hcnt
    have hrest := ih (emitToken fixedLitLenTable fixedDistTable w t)
      (fun t' ht' => hok t' (by simp [ht'])) ht.2.2 ht.2.1
    refine ⟨?_, hrest.2.1, hrest.2.2⟩
    rw [List.foldl_cons, hrest.1, ht.1, tokensBitsFixed, List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- L5-writer (fixed path): `emitTokens` emits exactly the tokens' ghost bits followed by
    the end-of-block symbol 256, preserving the writer invariant. -/
theorem writerBits_emitTokens_fixed (tokens : Array LZToken) (w : BitWriter)
    (hok : ∀ t ∈ tokens.toList, tokenRangesOk t)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    writerBits (emitTokens fixedLitLenTable fixedDistTable w tokens) =
      writerBits w ++ tokensBitsFixed tokens.toList ++ symbolBits fixedLitLenTable 256 ∧
    (emitTokens fixedLitLenTable fixedDistTable w tokens).bitCount < 8 ∧
    (emitTokens fixedLitLenTable fixedDistTable w tokens).bitBuf.toNat <
      2 ^ (emitTokens fixedLitLenTable fixedDistTable w tokens).bitCount := by
  unfold emitTokens
  have hfold : tokens.foldl (emitToken fixedLitLenTable fixedDistTable) w =
      tokens.toList.foldl (emitToken fixedLitLenTable fixedDistTable) w := by
    rw [Array.foldl_toList]
  rw [hfold]
  have h1 := writerBits_foldl_emitToken_fixed tokens.toList w hok hbuf hcnt
  obtain ⟨c256, l256, hc256, _, hl256, hv256, _⟩ := fixedLit_symbol_spec (sym := 256) (by omega)
  have h2 := writerBits_emitHuffSymbol _ fixedLitLenTable 256 c256 l256 hc256
    (by omega) hv256 h1.2.2 h1.2.1
  refine ⟨?_, h2.2.1, h2.2.2⟩
  rw [h2.1, h1.1]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- The empty writer has emitted no bits and satisfies the operating invariant. -/
theorem writerBits_empty : writerBits ({} : BitWriter) = [] ∧
    ({} : BitWriter).bitBuf.toNat < 2 ^ ({} : BitWriter).bitCount ∧
    ({} : BitWriter).bitCount < 8 := by
  refine ⟨?_, by simp, by simp⟩
  simp [writerBits, bytesBits, natBits]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- L7-writer (fixed path): the complete fixed-Huffman final block is the 3 header bits
    `BFINAL=1, BTYPE=01` (LSB-first: `true, true, false`), the tokens' ghost bits, and the
    end-of-block symbol — with the writer invariant available for `flushBitWriter`. -/
theorem writerBits_emitFixedBlock (tokens : Array LZToken)
    (hok : ∀ t ∈ tokens.toList, tokenRangesOk t) :
    writerBits (emitFixedBlock tokens) =
      true :: true :: false ::
        (tokensBitsFixed tokens.toList ++ symbolBits fixedLitLenTable 256) ∧
    (emitFixedBlock tokens).bitCount < 8 ∧
    (emitFixedBlock tokens).bitBuf.toNat < 2 ^ (emitFixedBlock tokens).bitCount := by
  unfold emitFixedBlock
  have he := writerBits_empty
  have h1 := writerBits_writeBits ({} : BitWriter) 1 1 he.2.1 (by omega) (by simp)
  have h2 := writerBits_writeBits (writeBits {} 1 1) 1 2 h1.2.2 (by omega) (by omega)
  have h3 := writerBits_emitTokens_fixed tokens (writeBits (writeBits {} 1 1) 1 2) hok
    h2.2.2 h2.2.1
  refine ⟨?_, h3.2.1, h3.2.2⟩
  rw [h3.1, h2.1, h1.1, he.1]
  rfl

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Every token the greedy tokenizer worker appends is RFC 1951 range-valid: refs come
    only from certified `matchValid` matches, literals are always valid. -/
theorem tokenizeAux_rangesOk (data : ByteArray) :
    ∀ (fuel pos : Nat) (acc : Array LZToken),
      (∀ t ∈ acc.toList, tokenRangesOk t) →
      ∀ t ∈ (tokenizeAux data fuel pos acc).toList, tokenRangesOk t := by
  intro fuel
  induction fuel with
  | zero => intro pos acc hacc; simpa [tokenizeAux] using hacc
  | succ fuel ih =>
    intro pos acc hacc
    simp only [tokenizeAux]
    split
    · split
      · rename_i hm
        apply ih
        intro t ht
        rw [Array.toList_push] at ht
        rcases List.mem_append.mp ht with h | h
        · exact hacc t h
        · have := List.mem_singleton.mp h
          subst this
          obtain ⟨h3, h258, h1d, h32768, _⟩ := matchValid_spec hm.2
          exact ⟨h3, h258, h1d, h32768⟩
      · apply ih
        intro t ht
        rw [Array.toList_push] at ht
        rcases List.mem_append.mp ht with h | h
        · exact hacc t h
        · have := List.mem_singleton.mp h
          subst this
          trivial
    · exact hacc

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Every token `tokenize` produces is RFC 1951 range-valid. -/
theorem tokenize_rangesOk (data : ByteArray) :
    ∀ t ∈ (tokenize data).toList, tokenRangesOk t := by
  unfold tokenize
  exact tokenizeAux_rangesOk data data.size 0 #[] (by simp)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- L7-reader entry (fixed path): a reader over the flushed fixed block sees exactly the
    3 header bits, the tokens' ghost bits, the end-of-block symbol, and byte-alignment
    zero padding — with the reader's operating invariant established. -/
theorem fixedBlock_readerBits (tokens : Array LZToken)
    (hok : ∀ t ∈ tokens.toList, tokenRangesOk t) :
    ∃ pad,
      readerBits (mkBitReader (flushBitWriter (emitFixedBlock tokens))) =
        true :: true :: false ::
          (tokensBitsFixed tokens.toList ++ symbolBits fixedLitLenTable 256 ++
           List.replicate pad false) ∧
      (mkBitReader (flushBitWriter (emitFixedBlock tokens))).bitBuf.toNat <
        2 ^ (mkBitReader (flushBitWriter (emitFixedBlock tokens))).bitCount ∧
      (mkBitReader (flushBitWriter (emitFixedBlock tokens))).bitCount < 8 := by
  have hw := writerBits_emitFixedBlock tokens hok
  have hr := readerBits_of_flushed (emitFixedBlock tokens) hw.2.2 hw.2.1
  have hm := readerBits_mkBitReader (flushBitWriter (emitFixedBlock tokens))
  refine ⟨(8 - (emitFixedBlock tokens).bitCount) % 8, ?_, hm.2.1, hm.2.2⟩
  rw [hr, hw.1]
  simp [List.append_assoc]


/-
## PA16 L5-reader (fixed path, per-token): decode inverts emission token by token

Each lemma matches the exact read sequence `decodeHuffmanStream`'s loop body issues for
one token, phrased over total functions only (`decodeHuffmanSymbol`, `readBits`): given a
reader whose ghost bits start with the token's emitted window, every read succeeds with
exactly the encoder's values and the decoder's table lookups reconstruct the token's
`len`/`dist`/byte exactly. The stream-level induction assembling these awaits the
`decodeHuffmanStream`/`decompress` well-founded conversion.
-/

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Reading back a conditional extra-bits window: recovers exactly the written value. -/
theorem readBits_extra (r : BitReader) (n v : Nat) (rest : List Bool)
    (hv : v < 2 ^ n) (hn : n ≤ 24)
    (hbits : readerBits r = natBits n v ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', (if n > 0 then readBits r n
           else (pure (r, 0) : Except ZlibError (BitReader × Nat))) = .ok (r', v) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  split
  · have hlen : n ≤ (readerBits r).length := by
      rw [hbits, List.length_append, natBits_length]
      omega
    obtain ⟨r', v', hok, hv', hwin, hdrop, hinv', hcnt', hbytes'⟩ :=
      readBits_spec r n hinv hcnt hn hlen
    have htake : (readerBits r).take n = natBits n v := by
      rw [hbits, List.take_left' (by rw [natBits_length])]
    have hveq : v' = v := natBits_inj hv' hv (by rw [hwin, htake])
    have hrest : readerBits r' = rest := by
      rw [hdrop, hbits, List.drop_left' (by rw [natBits_length])]
    subst hveq
    exact ⟨r', hok, hrest, hinv', hcnt', hbytes'⟩
  · rename_i hn0
    have h0 : n = 0 := by omega
    subst h0
    have hv0 : v = 0 := by omega
    subst hv0
    exact ⟨r, rfl, by simpa [natBits] using hbits, hinv, hcnt, rfl⟩

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decoding one literal token's bits under the fixed tables. -/
theorem decode_lit_fixed (b : UInt8) (r : BitReader) (rest : List Bool)
    (hbits : readerBits r = tokenBitsFixed (.lit b) ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r fixedLitLenTable = .ok (r', b.toNat) ∧ b.toNat < 256 ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  have hb : b.toNat < 256 := b.toNat_lt
  obtain ⟨r', hok, hrest, hinv', hcnt', hbytes'⟩ :=
    decodeHuffmanSymbol_fixedLit (sym := b.toNat) (by omega) r rest
      (by simpa [tokenBitsFixed] using hbits) hinv hcnt
  exact ⟨r', hok, hb, hrest, hinv', hcnt', hbytes'⟩

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decoding the end-of-block symbol's bits under the fixed tables. -/
theorem decode_eob_fixed (r : BitReader) (rest : List Bool)
    (hbits : readerBits r = symbolBits fixedLitLenTable 256 ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r fixedLitLenTable = .ok (r', 256) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes :=
  decodeHuffmanSymbol_fixedLit (sym := 256) (by omega) r rest hbits hinv hcnt

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decoding one back-reference token's bits under the fixed tables: the four reads the
    decoder issues (length symbol, length extras, distance symbol, distance extras) each
    succeed with exactly the encoder's values, the decoder's table lookups reconstruct
    `len` and `dist` exactly, and its guards (`sym ≤ 285`, `distSym < 30`) pass. -/
theorem decode_ref_fixed (len dist : Nat) (h3 : 3 ≤ len) (h258 : len ≤ 258)
    (h1d : 1 ≤ dist) (h32768 : dist ≤ 32768) (r : BitReader) (rest : List Bool)
    (hbits : readerBits r = tokenBitsFixed (.ref len dist) ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r1 r2 r3 r4 extraL extraD,
      decodeHuffmanSymbol r fixedLitLenTable = .ok (r1, (encodeLength len).1) ∧
      257 ≤ (encodeLength len).1 ∧ (encodeLength len).1 ≤ 285 ∧
      (if lengthTable[(encodeLength len).1 - 257]!.2 > 0
        then readBits r1 lengthTable[(encodeLength len).1 - 257]!.2
        else (pure (r1, 0) : Except ZlibError (BitReader × Nat))) = .ok (r2, extraL) ∧
      lengthTable[(encodeLength len).1 - 257]!.1 + extraL = len ∧
      decodeHuffmanSymbol r2 fixedDistTable = .ok (r3, (encodeDistance dist).1) ∧
      (encodeDistance dist).1 < 30 ∧
      (if distanceTable[(encodeDistance dist).1]!.2 > 0
        then readBits r3 distanceTable[(encodeDistance dist).1]!.2
        else (pure (r3, 0) : Except ZlibError (BitReader × Nat))) = .ok (r4, extraD) ∧
      distanceTable[(encodeDistance dist).1]!.1 + extraD = dist ∧
      readerBits r4 = rest ∧
      r4.bitBuf.toNat < 2 ^ r4.bitCount ∧ r4.bitCount < 8 ∧ r4.bytes = r.bytes := by
  obtain ⟨hL257, hL285, hLeb, hLev, hLbase, hLtbl⟩ := encodeLength_spec len (by omega) h3
  obtain ⟨hDc, hDeb, hDev, hDbase, hDtbl⟩ := encodeDistance_spec' dist h1d h32768
  -- reshape the bit stream into the four windows
  have hbits' : readerBits r =
      symbolBits fixedLitLenTable (encodeLength len).1 ++
        (natBits (encodeLength len).2.1 (encodeLength len).2.2 ++
          (symbolBits fixedDistTable (encodeDistance dist).1 ++
            (natBits (encodeDistance dist).2.1 (encodeDistance dist).2.2 ++ rest))) := by
    rw [hbits]
    simp [tokenBitsFixed, List.append_assoc]
  -- 1. length/literal symbol
  obtain ⟨r1, hok1, hrest1, hinv1, hcnt1, hbytes1⟩ :=
    decodeHuffmanSymbol_fixedLit (sym := (encodeLength len).1) (by omega) r _ hbits' hinv hcnt
  -- 2. length extra bits
  obtain ⟨r2, hok2, hrest2, hinv2, hcnt2, hbytes2⟩ :=
    readBits_extra r1 (encodeLength len).2.1 (encodeLength len).2.2 _ hLev (by omega)
      hrest1 hinv1 hcnt1
  -- 3. distance symbol
  obtain ⟨r3, hok3, hrest3, hinv3, hcnt3, hbytes3⟩ :=
    decodeHuffmanSymbol_fixedDist (sym := (encodeDistance dist).1) (by omega) r2 _
      hrest2 hinv2 hcnt2
  -- 4. distance extra bits
  obtain ⟨r4, hok4, hrest4, hinv4, hcnt4, hbytes4⟩ :=
    readBits_extra r3 (encodeDistance dist).2.1 (encodeDistance dist).2.2 rest hDev (by omega)
      hrest3 hinv3 hcnt3
  refine ⟨r1, r2, r3, r4, (encodeLength len).2.2, (encodeDistance dist).2.2,
    hok1, hL257, hL285, ?_, ?_, hok3, by omega, ?_, ?_, hrest4, hinv4, hcnt4, ?_⟩
  · rw [hLtbl]; exact hok2
  · rw [hLbase]
  · rw [hDtbl]; exact hok4
  · rw [hDbase]
  · rw [hbytes4, hbytes3, hbytes2, hbytes1]

/-
## PA16 L5/L7 (fixed path): the stream induction and the fixed-block roundtrip

With `decodeHuffmanStream`/`decompress` now total (branch-rooted `HuffmanTable`
invariant), the per-token decode lemmas assemble into the stream-level induction and the
universal fixed-block roundtrip. Scope is stated honestly: `emitFixedBlock_roundtrip_soundness`
covers the fixed-Huffman encoder for every input; `compress`'s dynamic branch is the
remaining obligation for the universal `deflate_roundtrip_soundness`.
-/

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Positional well-formedness of a token list: every back-reference's distance reaches
    only into output that exists when the token is decoded, starting from output length
    `pos`, plus the RFC 1951 ranges. -/
def tokensWF : List LZToken → Nat → Prop
  | [], _ => True
  | .lit _ :: ts, pos => tokensWF ts (pos + 1)
  | .ref len dist :: ts, pos =>
    3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 ∧ dist ≤ pos ∧ tokensWF ts (pos + len)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- The tokenizer's output, beyond any accumulator, is positionally well-formed at the
    position it started from. -/
theorem tokenizeAux_wf (data : ByteArray) :
    ∀ (fuel pos : Nat) (acc : Array LZToken),
      ∃ rest, (tokenizeAux data fuel pos acc).toList = acc.toList ++ rest ∧
        tokensWF rest pos := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos acc
    exact ⟨[], by simp [tokenizeAux], trivial⟩
  | succ fuel ih =>
    intro pos acc
    simp only [tokenizeAux]
    split
    · split
      · rename_i hm
        obtain ⟨rest, hlist, hwf⟩ := ih (pos + (findLongestMatch data pos).1)
          (acc.push (.ref (findLongestMatch data pos).1 (findLongestMatch data pos).2))
        refine ⟨.ref (findLongestMatch data pos).1 (findLongestMatch data pos).2 :: rest, ?_, ?_⟩
        · rw [hlist, Array.toList_push]
          simp
        · obtain ⟨h3, h258, h1d, h32768, hdp, _⟩ := matchValid_spec hm.2
          exact ⟨h3, h258, h1d, h32768, hdp, hwf⟩
      · obtain ⟨rest, hlist, hwf⟩ := ih (pos + 1) (acc.push (.lit (data.get! pos)))
        refine ⟨.lit (data.get! pos) :: rest, ?_, hwf⟩
        rw [hlist, Array.toList_push]
        simp
    · exact ⟨[], by simp, trivial⟩

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- `tokenize`'s output is positionally well-formed from an empty output. -/
theorem tokenize_wf (data : ByteArray) : tokensWF (tokenize data).toList 0 := by
  obtain ⟨rest, hlist, hwf⟩ := tokenizeAux_wf data data.size 0 #[]
  unfold tokenize
  rw [hlist]
  simpa using hwf

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The decoder's imperative back-reference copy loop is exactly the reference `lzCopy`. -/
theorem idrun_copy_eq_lzCopy (dist : Nat) :
    ∀ (n : Nat) (out : ByteArray),
      (Id.run do
        let mut acc := out
        for _ in [0:n] do
          let srcIdx := acc.size - dist
          acc := acc.push (acc.get! srcIdx)
        acc) = lzCopy dist n out := by
  have hfold : ∀ (n : Nat) (out : ByteArray),
      (Id.run do
        let mut acc := out
        for _ in [0:n] do
          let srcIdx := acc.size - dist
          acc := acc.push (acc.get! srcIdx)
        acc) =
      (List.range' 0 n 1).foldl (fun acc _ => acc.push (acc.get! (acc.size - dist))) out := by
    intro n out
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
    simp
  have hgen : ∀ (l : List Nat) (out : ByteArray),
      l.foldl (fun acc _ => acc.push (acc.get! (acc.size - dist))) out =
        lzCopy dist l.length out := by
    intro l
    induction l with
    | nil => intro out; simp [lzCopy]
    | cons x xs ih =>
      intro out
      rw [List.foldl_cons, ih, List.length_cons, lzCopy]
  intro n out
  rw [hfold, hgen, List.length_range']

set_option maxHeartbeats 1000000 in
/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- L5 (fixed path): the decoder's stream loop, fed exactly the bits `emitTokens` wrote
    for a positionally well-formed token list, terminates at the end-of-block symbol having
    expanded exactly those tokens, consuming exactly those bits. -/
theorem decodeHuffmanStream_go_fixed
    (hL : ∃ l rr, fixedLitLenTable.root = HuffmanNode.branch l rr)
    (hD : ∃ l rr, fixedDistTable.root = HuffmanNode.branch l rr) :
    ∀ (ts : List LZToken) (r : BitReader) (curOut : ByteArray) (rest : List Bool),
      tokensWF ts curOut.size →
      readerBits r = tokensBitsFixed ts ++ (symbolBits fixedLitLenTable 256 ++ rest) →
      r.bitBuf.toNat < 2 ^ r.bitCount → r.bitCount < 8 →
      ∃ r', decodeHuffmanStream.go fixedLitLenTable fixedDistTable r curOut hL hD =
          .ok (r', ts.foldl expandToken curOut) ∧
        readerBits r' = rest ∧
        r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  intro ts
  induction ts with
  | nil =>
    intro r curOut rest hwf hbits hinv hcnt
    obtain ⟨rE, hokE, hrestE, hinvE, hcntE, hbytesE⟩ :=
      decode_eob_fixed r rest (by simpa [tokensBitsFixed] using hbits) hinv hcnt
    refine ⟨rE, ?_, hrestE, hinvE, hcntE, hbytesE⟩
    rw [decodeHuffmanStream.go.eq_def]
    split
    · rename_i e heq
      rw [heq] at hokE
      exact absurd hokE (by simp)
    · rename_i nextR sym heq
      rw [heq] at hokE
      simp only [Except.ok.injEq, Prod.mk.injEq] at hokE
      obtain ⟨h1, h2⟩ := hokE
      subst h1
      subst h2
      rw [if_neg (by omega : ¬ (256 : Nat) < 256), if_pos (by decide : ((256:Nat) == 256) = true)]
      rfl
  | cons t ts ih =>
    intro r curOut rest hwf hbits hinv hcnt
    cases t with
    | lit b =>
      have hbits1 : readerBits r = tokenBitsFixed (.lit b) ++
          (tokensBitsFixed ts ++ (symbolBits fixedLitLenTable 256 ++ rest)) := by
        rw [hbits, tokensBitsFixed]
        simp [List.append_assoc]
      obtain ⟨r1, hok1, hb256, hrest1, hinv1, hcnt1, hbytes1⟩ :=
        decode_lit_fixed b r _ hbits1 hinv hcnt
      have hwf' : tokensWF ts (curOut.push b).size := by
        rw [ByteArray.size_push]
        exact hwf
      obtain ⟨r', hok', hrest', hinv', hcnt', hbytes'⟩ :=
        ih r1 (curOut.push b) rest hwf' hrest1 hinv1 hcnt1
      refine ⟨r', ?_, hrest', hinv', hcnt', by rw [hbytes', hbytes1]⟩
      rw [decodeHuffmanStream.go.eq_def]
      split
      · rename_i e heq
        rw [heq] at hok1
        exact absurd hok1 (by simp)
      · rename_i nextR sym heq
        rw [heq] at hok1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
        obtain ⟨h1, h2⟩ := hok1
        subst h1
        subst h2
        rw [if_pos hb256, List.foldl_cons]
        have hpush : b.toNat.toUInt8 = b := UInt8.ofNat_toNat
        rw [hpush]
        exact hok'
    | ref len dist =>
      obtain ⟨h3, h258, h1d, h32768, hdlepos, hwfrest⟩ := hwf
      have hbits1 : readerBits r = tokenBitsFixed (.ref len dist) ++
          (tokensBitsFixed ts ++ (symbolBits fixedLitLenTable 256 ++ rest)) := by
        rw [hbits, tokensBitsFixed]
        simp [List.append_assoc]
      obtain ⟨r1, r2, r3, r4, extraL, extraD, hok1, hs257, hs285, hok2, hbase, hok3,
        hd30, hok4, hdbase, hrest4, hinv4, hcnt4, hbytes4⟩ :=
        decode_ref_fixed len dist h3 h258 h1d h32768 r _ hbits1 hinv hcnt
      have hwf' : tokensWF ts (lzCopy dist len curOut).size := by
        rw [lzCopy_size]
        exact hwfrest
      obtain ⟨r', hok', hrest', hinv', hcnt', hbytes'⟩ :=
        ih r4 (lzCopy dist len curOut) rest hwf' hrest4 hinv4 hcnt4
      refine ⟨r', ?_, hrest', hinv', hcnt', by rw [hbytes', hbytes4]⟩
      rw [decodeHuffmanStream.go.eq_def]
      split
      · rename_i e heq
        rw [heq] at hok1
        exact absurd hok1 (by simp)
      · rename_i nextR sym heq
        rw [heq] at hok1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
        obtain ⟨h1, h2⟩ := hok1
        subst h1
        subst h2
        rw [if_neg (by omega : ¬ (encodeLength len).1 < 256),
          if_neg (by simp; omega), if_pos (by omega : (encodeLength len).1 ≤ 285)]
        dsimp only
        split
        · rename_i e heq2
          rw [heq2] at hok2
          exact absurd hok2 (by simp)
        · rename_i rLen extraVal heq2
          rw [heq2] at hok2
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok2
          obtain ⟨h1, h2⟩ := hok2
          subst h1
          subst h2
          split
          · rename_i e heq3
            rw [heq3] at hok3
            exact absurd hok3 (by simp)
          · rename_i rDistSym distSym heq3
            rw [heq3] at hok3
            simp only [Except.ok.injEq, Prod.mk.injEq] at hok3
            obtain ⟨h1, h2⟩ := hok3
            subst h1
            subst h2
            rw [if_neg (by omega : ¬ (encodeDistance dist).1 ≥ 30)]
            split
            · rename_i e heq4
              rw [heq4] at hok4
              exact absurd hok4 (by simp)
            · rename_i rDist distExtraVal heq4
              rw [heq4] at hok4
              simp only [Except.ok.injEq, Prod.mk.injEq] at hok4
              obtain ⟨h1, h2⟩ := hok4
              subst h1
              subst h2
              rw [hdbase, hbase]
              rw [if_neg (by simp; omega)]
              rw [idrun_copy_eq_lzCopy, List.foldl_cons]
              exact hok'

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Positional well-formedness implies plain range validity for every token. -/
theorem tokensWF_rangesOk : ∀ (ts : List LZToken) (pos : Nat), tokensWF ts pos →
    ∀ t ∈ ts, tokenRangesOk t := by
  intro ts
  induction ts with
  | nil => intro pos _ t ht; simp at ht
  | cons t0 ts ih =>
    intro pos hwf t ht
    have hsplit : tokenRangesOk t0 ∧ (∀ t' ∈ ts, tokenRangesOk t') := by
      cases t0 with
      | lit b => exact ⟨trivial, ih (pos + 1) hwf⟩
      | ref len dist =>
        obtain ⟨h3, h258, h1d, h32768, _, hrest⟩ := hwf
        exact ⟨⟨h3, h258, h1d, h32768⟩, ih (pos + len) hrest⟩
    rcases List.mem_cons.mp ht with rfl | hmem
    · exact hsplit.1
    · exact hsplit.2 t hmem

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeHuffmanStream` (top-level) on a fixed-table stream, from `go`'s induction. -/
theorem decodeHuffmanStream_fixed
    (hL : ∃ l rr, fixedLitLenTable.root = HuffmanNode.branch l rr)
    (hD : ∃ l rr, fixedDistTable.root = HuffmanNode.branch l rr)
    (ts : List LZToken) (r : BitReader) (curOut : ByteArray) (rest : List Bool)
    (hwf : tokensWF ts curOut.size)
    (hbits : readerBits r = tokensBitsFixed ts ++ (symbolBits fixedLitLenTable 256 ++ rest))
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanStream r fixedLitLenTable fixedDistTable hL hD curOut =
        .ok (r', ts.foldl expandToken curOut) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  unfold decodeHuffmanStream
  exact decodeHuffmanStream_go_fixed hL hD ts r curOut rest hwf hbits hinv hcnt

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- L7 (fixed block): `decompress` of a flushed `emitFixedBlock` recovers exactly the
    expansion of the emitted tokens. -/
theorem decompress_fixedBlock (tokens : Array LZToken)
    (hwf : tokensWF tokens.toList 0) :
    decompress (flushBitWriter (emitFixedBlock tokens)) = .ok (expandTokens tokens) := by
  have hok : ∀ t ∈ tokens.toList, tokenRangesOk t := tokensWF_rangesOk _ 0 hwf
  obtain ⟨pad, hbits, hinv, hcnt⟩ := fixedBlock_readerBits tokens hok
  unfold decompress
  rw [decompress.go.eq_def]
  -- BFINAL: 1 bit, value 1
  have hlen1 : 1 ≤ (readerBits (mkBitReader (flushBitWriter (emitFixedBlock tokens)))).length := by
    rw [hbits]; simp
  obtain ⟨rB, v1, hok1, hv1, hwin1, hdrop1, hinv1, hcnt1, _⟩ :=
    readBits_spec (mkBitReader (flushBitWriter (emitFixedBlock tokens))) 1 hinv hcnt
      (by omega) hlen1
  have hv1' : v1 = 1 := by
    apply natBits_inj hv1 (by decide : (1:Nat) < 2 ^ 1)
    rw [hwin1, hbits]
    rfl
  subst hv1'
  have hdrop1' : readerBits rB = true :: false ::
      (tokensBitsFixed tokens.toList ++ symbolBits fixedLitLenTable 256 ++
        List.replicate pad false) := by
    rw [hdrop1, hbits]
    rfl
  -- BTYPE: 2 bits, value 1
  have hlen2 : 2 ≤ (readerBits rB).length := by
    rw [hdrop1']; simp
  obtain ⟨rT, v2, hok2, hv2, hwin2, hdrop2, hinv2, hcnt2, _⟩ :=
    readBits_spec rB 2 hinv1 hcnt1 (by omega) hlen2
  have hv2' : v2 = 1 := by
    apply natBits_inj hv2 (by decide : (1:Nat) < 2 ^ 2)
    rw [hwin2, hdrop1']
    rfl
  subst hv2'
  have hdrop2' : readerBits rT = tokensBitsFixed tokens.toList ++
      (symbolBits fixedLitLenTable 256 ++ List.replicate pad false) := by
    rw [hdrop2, hdrop1']
    simp [List.append_assoc]
  -- the stream decode result, obtained while `rT` is still in scope
  obtain ⟨r', hstream', hrest', hinv', hcnt', _⟩ :=
    decodeHuffmanStream_fixed (buildHuffmanTable_isBranch fixedLitLenLengths 9)
      (buildHuffmanTable_isBranch fixedDistLengths 5) tokens.toList rT ByteArray.empty
      (List.replicate pad false) (by simpa using hwf) hdrop2' hinv2 hcnt2
  -- reduce the outer match chain
  split
  · rename_i e heq
    rw [heq] at hok1
    exact absurd hok1 (by simp)
  · rename_i rBfinal bfinal heq
    rw [heq] at hok1
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
    obtain ⟨hh1, hh2⟩ := hok1
    subst hh1
    subst hh2
    split
    · rename_i e heq2
      rw [heq2] at hok2
      exact absurd hok2 (by simp)
    · rename_i rBtype btype heq2
      rw [heq2] at hok2
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok2
      obtain ⟨hh1, hh2⟩ := hok2
      subst hh1
      subst hh2
      -- `match btype` with btype := 1: four literal branches, three impossible
      split
      · rename_i heqb hx
        exact absurd heqb (by decide)
      · -- btype = 1: the fixed-Huffman block branch
        split
        · rename_i e heq3
          have hcontra : (Except.ok (r', tokens.toList.foldl expandToken ByteArray.empty) :
              Except ZlibError (BitReader × ByteArray)) = .error e := by
            rw [← hstream']
            exact heq3
          exact absurd hcontra (by simp)
        · rename_i nextR nextOut heq3
          have hcomb : (Except.ok (r', tokens.toList.foldl expandToken ByteArray.empty) :
              Except ZlibError (BitReader × ByteArray)) = .ok (nextR, nextOut) := by
            rw [← hstream']
            exact heq3
          simp only [Except.ok.injEq, Prod.mk.injEq] at hcomb
          obtain ⟨hh1, hh2⟩ := hcomb
          rw [if_pos (by decide : ((1:Nat) == 1) = true)]
          rw [← hh2]
          unfold expandTokens
          rw [Array.foldl_toList]
      · rename_i heqb hx
        exact absurd heqb (by decide)
      · rename_i h0 h1 h2
        exact (h1 heq2 rfl HEq.rfl).elim

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- **Fixed-Huffman DEFLATE roundtrip soundness, universal over the input** (PA16 L7,
    fixed-block encoder only — NOT a statement about `compress`'s dynamic branch): for
    EVERY `ByteArray`, inflating the flushed fixed-Huffman block emitted for its greedy
    LZ77 tokenization returns exactly the original bytes. -/
theorem emitFixedBlock_roundtrip_soundness (data : ByteArray) :
    decompress (flushBitWriter (emitFixedBlock (tokenize data))) = .ok data := by
  rw [decompress_fixedBlock (tokenize data) (tokenize_wf data),
    lz77_roundtrip_soundness data]

end Grass.Std.Zlib.Deflate
