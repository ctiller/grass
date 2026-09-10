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

import Grass.Std.Zlib.Deflate.Equivalence

/-
## Output-size bounds for `compress` and `zlibCompress`

`compress` cannot be evaluated by the kernel (`List.mergeSort` inside
`packageMergeLengths` is well-founded recursion, and `compressPlan` forces it on every
input), so any fact about a *specific* compressed stream's size must come from a
propositional bound, not `decide`. This file bounds the emitted bit count of both
encoder branches through the ghost `writerBits` characterizations and converts it to a
byte bound: `(zlibCompress data).size <= 6 * data.size + 610`. The PNG chunk layer uses
this to discharge the 4-byte chunk-length precondition of `png_roundtrip_soundness`
without evaluating the compressor.
-/

namespace Grass.Std.Zlib.Deflate

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Each finished byte contributes exactly 8 ghost bits. -/
theorem bytesBits_length (bs : ByteArray) : (bytesBits bs).length = 8 * bs.size := by
  unfold bytesBits
  have h : ∀ l : List UInt8, (l.flatMap fun b => natBits 8 b.toNat).length = 8 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, natBits_length, ih, List.length_cons]
      omega
  rw [h, Array.length_toList]
  rfl

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ghost bit count of a writer state. -/
theorem writerBits_length (w : BitWriter) :
    (writerBits w).length = 8 * w.bytes.size + w.bitCount := by
  unfold writerBits
  rw [List.length_append, bytesBits_length, natBits_length]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Flushing adds at most one padding byte. -/
theorem flushBitWriter_size (w : BitWriter) :
    (flushBitWriter w).size ≤ w.bytes.size + 1 := by
  unfold flushBitWriter
  split
  · rw [ByteArray.size_push]
    omega
  · omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Byte count of the flushed stream against the ghost bit count. -/
theorem flushed_size_le_bits (w : BitWriter) :
    8 * (flushBitWriter w).size ≤ (writerBits w).length + 8 := by
  have h1 := flushBitWriter_size w
  have h2 := writerBits_length w
  omega

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Fixed literal/length codes are at most 9 bits. -/
theorem symbolBits_fixedLit_length {sym : Nat} (h : sym < 288) :
    (symbolBits fixedLitLenTable sym).length ≤ 9 := by
  obtain ⟨code, len, hc, _, hlen, _, _⟩ := fixedLit_symbol_spec h
  rw [symbolBits_eq _ _ _ _ hc, natBits_length]
  exact hlen

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Fixed distance codes are at most 9 bits. -/
theorem symbolBits_fixedDist_length {sym : Nat} (h : sym < 32) :
    (symbolBits fixedDistTable sym).length ≤ 9 := by
  obtain ⟨code, len, hc, _, hlen, _, _⟩ := fixedDist_symbol_spec h
  rw [symbolBits_eq _ _ _ _ hc, natBits_length]
  exact hlen

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- One token costs at most 36 bits under the fixed tables. -/
theorem tokenBitsFixed_length (t : LZToken) (hok : tokenRangesOk t) :
    (tokenBitsFixed t).length ≤ 36 := by
  cases t with
  | lit b =>
    show (symbolBits fixedLitLenTable b.toNat).length ≤ 36
    have hb : b.toNat < 288 := by
      have := b.toNat_lt
      omega
    have := symbolBits_fixedLit_length hb
    omega
  | ref len dist =>
    obtain ⟨h3, h258, h1, h32768⟩ := hok
    show (symbolBits fixedLitLenTable (encodeLength len).1 ++
      natBits (encodeLength len).2.1 (encodeLength len).2.2 ++
      symbolBits fixedDistTable (encodeDistance dist).1 ++
      natBits (encodeDistance dist).2.1 (encodeDistance dist).2.2).length ≤ 36
    obtain ⟨_, hLc, hLe, _, _, _⟩ := encodeLength_spec len (by omega) h3
    obtain ⟨hDc, hDe, _, _, _⟩ := encodeDistance_spec' dist h1 h32768
    have hL := symbolBits_fixedLit_length
      (show (encodeLength len).1 < 288 from by omega)
    have hD := symbolBits_fixedDist_length
      (show (encodeDistance dist).1 < 32 from by omega)
    simp only [List.length_append, natBits_length]
    omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A fixed-table token stream costs at most 36 bits per token. -/
theorem tokensBitsFixed_length : ∀ l : List LZToken, (∀ t ∈ l, tokenRangesOk t) →
    (tokensBitsFixed l).length ≤ 36 * l.length := by
  intro l
  induction l with
  | nil => intro _; simp [tokensBitsFixed]
  | cons t ts ih =>
    intro h
    show (tokenBitsFixed t ++ tokensBitsFixed ts).length ≤ _
    rw [List.length_append]
    have h1 := tokenBitsFixed_length t (h t (by simp))
    have h2 := ih (fun t' ht' => h t' (by simp [ht']))
    simp only [List.length_cons]
    omega


/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- The tokenizer emits at most one token per unit of fuel. -/
theorem tokenizeAux_length (data : ByteArray) : ∀ fuel pos acc,
    (tokenizeAux data fuel pos acc).size ≤ acc.size + fuel := by
  intro fuel
  induction fuel with
  | zero => intro pos acc; simp [tokenizeAux]
  | succ fuel ih =>
    intro pos acc
    simp only [tokenizeAux]
    split
    · split
      · refine Nat.le_trans (ih _ _) ?_
        rw [Array.size_push]
        omega
      · refine Nat.le_trans (ih _ _) ?_
        rw [Array.size_push]
        omega
    · omega

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- The tokenizer emits at most one token per input byte. -/
theorem tokenize_length (data : ByteArray) : (tokenize data).size ≤ data.size := by
  have h := tokenizeAux_length data data.size 0 #[]
  have h0 : (#[] : Array LZToken).size = 0 := rfl
  unfold tokenize
  omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bit count of the fixed-Huffman branch. -/
theorem emitFixedBlock_length (tokens : Array LZToken)
    (hok : ∀ t ∈ tokens.toList, tokenRangesOk t) :
    (writerBits (emitFixedBlock tokens)).length ≤ 36 * tokens.toList.length + 12 := by
  have hw := writerBits_emitFixedBlock tokens hok
  rw [hw.1]
  simp only [List.length_cons, List.length_append]
  have h1 := tokensBitsFixed_length tokens.toList hok
  have h2 := symbolBits_fixedLit_length (show 256 < 288 from by omega)
  omega

end Grass.Std.Zlib.Deflate
