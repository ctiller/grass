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

/-!
# PA16 L3/L6 and the fixed-block connection theorem (Law 12)

`Stdlib/Zlib/Deflate.lean` carries two fixed-Huffman encoders: `compressFixed`, which
`gzipCompress` calls and the x86-64/Wasm machine engines implement, and the
`tokenize`/`emitFixedBlock` pair every PA16 roundtrip theorem is stated about. They were
unlinked twins (Law 12) -- `compressFixed` occurred at exactly two sites tree-wide, its
definition and its single call site, with nothing connecting it to the proof surface. This
module builds that connection:

* **L3** (`findLongestMatch_matchValid`) -- the match search only ever reports genuine RFC 1951
  back-references, so the tokenizer's `matchValid` guard is redundant and the two encoders
  make the same accept/reject decision at every position.
* **L6a/L6b/L6c** (`fixedLitCode_spec`, `cfLen_spec`, `fixedDistCode_spec`) -- `compressFixed`'s
  four hardcoded code formulas and its inline length-band formula agree with the fixed tables
  and `encodeLength` on their whole finite domains.
* **Fusion** (`tokenize_emit_eq`) -- `compressFixed`'s single inline loop is `tokenize`
  followed by a fold of `emitToken`.
* **The connection theorem** (`compressFixed_eq_emitFixedBlock`) and its payoff
  (`compressFixed_roundtrip_soundness`).

Everything here is kernel-checked structural proof on the standard three axioms; the two
finite `decide` closures (288 and 32 symbols, 256 lengths) are exhaustive over their actual
domains, so they are rung 2 of `docs/REVIEW.md` Law 10 and need no allowlist entry.

This does NOT retire any `scripts/gate_allowlist.txt` entry. The seven Spike 5 entries need
the gzip *container* framing (PA16 L8) on top of this, and their pointwise `native_decide`
form is additionally blocked from `decide` by `decompress`'s well-founded recursion, whose
`Acc.rec` does not reduce in the kernel.
-/

namespace Grass.Std.Zlib.Deflate



theorem matchExtend_spec (data : ByteArray) (pos candidate maxMatchLen : Nat) :
    ∀ fuel len, len ≤ maxMatchLen →
      (∀ j, len ≤ j → j < matchExtend data pos candidate maxMatchLen fuel len →
        data.get! (candidate + j) = data.get! (pos + j))
      ∧ len ≤ matchExtend data pos candidate maxMatchLen fuel len
      ∧ matchExtend data pos candidate maxMatchLen fuel len ≤ maxMatchLen := by
  intro fuel
  induction fuel with
  | zero =>
    intro len h
    refine ⟨?_, Nat.le_refl _, h⟩
    intro j h1 h2; simp only [matchExtend] at h2; omega
  | succ n ih =>
    intro len h
    cases hg : (decide (len < maxMatchLen) &&
        data.get! (candidate + len) == data.get! (pos + len)) with
    | false =>
      have hstep : matchExtend data pos candidate maxMatchLen (n + 1) len = len := by
        simp only [matchExtend, hg]; rfl
      refine ⟨?_, ?_, ?_⟩
      · intro j h1 h2; rw [hstep] at h2; omega
      · rw [hstep]; exact Nat.le_refl _
      · rw [hstep]; exact h
    | true =>
      have hlt : len < maxMatchLen := by simp at hg; omega
      have heq : data.get! (candidate + len) = data.get! (pos + len) := by simp at hg; exact hg.2
      have hstep : matchExtend data pos candidate maxMatchLen (n + 1) len
          = matchExtend data pos candidate maxMatchLen n (len + 1) := by
        simp only [matchExtend, hg]; rfl
      obtain ⟨hall, hge, hle⟩ := ih (len + 1) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro j h1 h2
        rw [hstep] at h2
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
        · exact heq
        · exact hall j (by omega) h2
      · rw [hstep]; omega
      · rw [hstep]; exact hle

/-- The RFC 1951 match-validity facts `matchValid` certifies, as a Prop. -/
def MOK (data : ByteArray) (pos len dist : Nat) : Prop :=
  3 ≤ len → (len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 ∧ dist ≤ pos ∧ pos + len ≤ data.size ∧
             ∀ i, i < len → data.get! (pos - dist + i) = data.get! (pos + i))

/-- `MOK` on a (len, dist) pair. -/
def MOKp (data : ByteArray) (pos : Nat) (r : Nat × Nat) : Prop := MOK data pos r.1 r.2

/-- PA16 L3, outer half: the candidate scan only ever returns certified matches. -/
theorem matchScan_ok (data : ByteArray) (pos startLookback maxMatchLen : Nat)
    (hmm3 : 3 ≤ maxMatchLen) (hmm258 : maxMatchLen ≤ 258)
    (hmmsz : pos + maxMatchLen ≤ data.size)
    (hsl : pos - startLookback ≤ 32768) :
    ∀ fuel candidate bestLen bestDist, candidate ≤ pos → MOK data pos bestLen bestDist →
      MOKp data pos (matchScan data pos startLookback maxMatchLen fuel candidate bestLen bestDist) := by
  intro fuel
  induction fuel with
  | zero => intro candidate bestLen bestDist _ hok; simp only [matchScan]; exact hok
  | succ n ih =>
    intro candidate bestLen bestDist hcp hok
    by_cases hgt : candidate > startLookback
    · by_cases h3 : (data.get! (candidate - 1) == data.get! pos &&
          data.get! (candidate - 1 + 1) == data.get! (pos + 1) &&
          data.get! (candidate - 1 + 2) == data.get! (pos + 2)) = true
      · obtain ⟨hall, hge3, hlemm⟩ :=
          matchExtend_spec data pos (candidate - 1) maxMatchLen (maxMatchLen - 3) 3 (by omega)
        have hprefix : ∀ i, i < 3 → data.get! (candidate - 1 + i) = data.get! (pos + i) := by
          intro i hi
          simp only [Bool.and_eq_true, beq_iff_eq] at h3
          have h012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases h012 with rfl | rfl | rfl
          · simpa using h3.1.1
          · exact h3.1.2
          · exact h3.2
        have hnew : MOK data pos
            (matchExtend data pos (candidate - 1) maxMatchLen (maxMatchLen - 3) 3)
            (pos - (candidate - 1)) := by
          intro _
          refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
          intro i hi
          have hs : pos - (pos - (candidate - 1)) = candidate - 1 := by omega
          rw [hs]
          by_cases h : i < 3
          · exact hprefix i h
          · exact hall i (by omega) hi
        by_cases hbetter :
            matchExtend data pos (candidate - 1) maxMatchLen (maxMatchLen - 3) 3 > bestLen
        · by_cases h258 :
              (matchExtend data pos (candidate - 1) maxMatchLen (maxMatchLen - 3) 3 == 258) = true
          · simp only [matchScan, if_pos hgt, if_pos h3, if_pos hbetter, if_pos h258]
            exact hnew
          · simp only [matchScan, if_pos hgt, if_pos h3, if_pos hbetter, if_neg h258]
            exact ih (candidate - 1) _ _ (by omega) hnew
        · simp only [matchScan, if_pos hgt, if_pos h3, if_neg hbetter]
          exact ih (candidate - 1) bestLen bestDist (by omega) hok
      · simp only [matchScan, if_pos hgt, if_neg h3]
        exact ih (candidate - 1) bestLen bestDist (by omega) hok
    · simp only [matchScan, if_neg hgt]
      exact hok

/-- **PA16 L3**: every match `findLongestMatch` reports at the tokenizer's call site is a
    genuine RFC 1951 back-reference -- the search's `matchLen >= 3` acceptance already implies
    `matchValid`. -/
theorem findLongestMatch_valid (data : ByteArray) (pos : Nat) :
    MOKp data pos (findLongestMatch data pos 32768 128) := by
  simp only [findLongestMatch]
  by_cases hshort : pos + 3 > data.size
  · simp only [if_pos hshort]; intro h; omega
  · simp only [if_neg hshort]
    have hm3 : 3 ≤ Nat.min 258 (data.size - pos) := by
      unfold Nat.min; rw [Nat.min_def]; split <;> omega
    have hm258 : Nat.min 258 (data.size - pos) ≤ 258 := by
      unfold Nat.min; rw [Nat.min_def]; split <;> omega
    have hmsz : pos + Nat.min 258 (data.size - pos) ≤ data.size := by
      unfold Nat.min; rw [Nat.min_def]; split <;> omega
    have hok := matchScan_ok data pos
      (if pos > 32768 then pos - 32768 else 0) (Nat.min 258 (data.size - pos))
      hm3 hm258 hmsz (by split <;> omega)
      128 pos 0 0 (Nat.le_refl _) (by intro h; omega)
    by_cases hb : (matchScan data pos (if pos > 32768 then pos - 32768 else 0)
        (Nat.min 258 (data.size - pos)) 128 pos 0 0).1 >= 3
    · simp only [if_pos hb]; exact hok
    · simp only [if_neg hb]; intro h; omega

/-- `MOK` is exactly what `matchValid` decides. -/
theorem matchValid_of_MOK {data : ByteArray} {pos len dist : Nat}
    (h : MOK data pos len dist) (h3 : 3 <= len) : matchValid data pos len dist = true := by
  obtain ⟨h258, hd1, hd2, hdp, hsz, hbytes⟩ := h h3
  simp only [matchValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨h3, h258⟩, hd1⟩, hd2⟩, hdp⟩, hsz⟩, ?_⟩
  intro i hi
  simp only [beq_iff_eq]
  exact hbytes i (List.mem_range.mp hi)

/-- The tokenizer's `matchValid` guard is redundant: `3 <= matchLen` already implies it. -/
theorem findLongestMatch_matchValid (data : ByteArray) (pos : Nat)
    (h3 : 3 <= (findLongestMatch data pos 32768 128).1) :
    matchValid data pos (findLongestMatch data pos 32768 128).1
      (findLongestMatch data pos 32768 128).2 = true :=
  matchValid_of_MOK (findLongestMatch_valid data pos) h3




def cfLenTriple (matchLen : Nat) : Nat × Nat × Nat :=
  if matchLen == 258 then (285, 0, 0)
  else if matchLen <= 10 then (257 + matchLen - 3, 0, 0)
  else if matchLen <= 18 then (265 + (matchLen - 11) / 2, 1, (matchLen - 11) &&& 1)
  else if matchLen <= 34 then (269 + (matchLen - 19) / 4, 2, (matchLen - 19) &&& 3)
  else if matchLen <= 66 then (273 + (matchLen - 35) / 8, 3, (matchLen - 35) &&& 7)
  else if matchLen <= 130 then (277 + (matchLen - 67) / 16, 4, (matchLen - 67) &&& 15)
  else (281 + (matchLen - 131) / 32, 5, (matchLen - 131) &&& 31)

def cfLenCheck : Bool :=
  (List.range 256).all (fun i => cfLenTriple (i + 3) == encodeLength (i + 3))

set_option maxRecDepth 40000 in
theorem cfLen_check : cfLenCheck = true := by decide

theorem cfLen_spec {len : Nat} (h3 : 3 ≤ len) (h258 : len ≤ 258) :
    cfLenTriple len = encodeLength len := by
  have hc := cfLen_check
  simp only [cfLenCheck, List.all_eq_true] at hc
  have := hc (len - 3) (List.mem_range.mpr (by omega))
  have hr : len - 3 + 3 = len := by omega
  rw [hr] at this
  simpa using this

def fixedLitCodeCheck : Bool :=
  (List.range 288).all (fun s =>
    fixedLitLenTable.codes[s]! ==
      (if s <= 143 then some (s + 0x30, 8)
       else if s <= 255 then some (s - 144 + 0x190, 9)
       else if s <= 279 then some (s - 256, 7)
       else some (s - 280 + 0xC0, 8)))

set_option maxRecDepth 40000 in
theorem fixedLitCode_check : fixedLitCodeCheck = true := by
  simp only [fixedLitCodeCheck, fixedLitLenTable, fixedLitLenLengths, buildHuffmanTable,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  decide

theorem fixedLitCode_spec {s : Nat} (hs : s < 288) :
    fixedLitLenTable.codes[s]! =
      (if s <= 143 then some (s + 0x30, 8)
       else if s <= 255 then some (s - 144 + 0x190, 9)
       else if s <= 279 then some (s - 256, 7)
       else some (s - 280 + 0xC0, 8)) := by
  have hc := fixedLitCode_check
  simp only [fixedLitCodeCheck, List.all_eq_true] at hc
  simpa using hc s (List.mem_range.mpr hs)

def fixedDistCodeCheck : Bool :=
  (List.range 32).all (fun c => fixedDistTable.codes[c]! == some (c, 5))

set_option maxRecDepth 20000 in
theorem fixedDistCode_check : fixedDistCodeCheck = true := by
  simp only [fixedDistCodeCheck, fixedDistTable, fixedDistLengths, buildHuffmanTable,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  decide

theorem fixedDistCode_spec {c : Nat} (hc : c < 32) :
    fixedDistTable.codes[c]! = some (c, 5) := by
  have h := fixedDistCode_check
  simp only [fixedDistCodeCheck, List.all_eq_true] at h
  simpa using h c (List.mem_range.mpr hc)

/-- Literal emission: the fixed table reproduces `compressFixedLoop`'s two hardcoded forms. -/
theorem emitToken_lit_eq (w : BitWriter) (b : UInt8) :
    emitToken fixedLitLenTable fixedDistTable w (.lit b)
      = (if b.toNat <= 143 then writeBits w (reverseBits (b.toNat + 0x30) 8) 8
         else writeBits w (reverseBits (b.toNat - 144 + 0x190) 9) 9) := by
  have hb : b.toNat < 288 := by
    have := b.toNat_lt_size
    simp only [UInt8.size] at this
    omega
  have hb255 : b.toNat ≤ 255 := by
    have := b.toNat_lt_size
    simp only [UInt8.size] at this
    omega
  simp only [emitToken, emitHuffSymbol, fixedLitCode_spec hb]
  by_cases h : b.toNat ≤ 143
  · simp only [if_pos h]
  · simp only [if_neg h, if_pos hb255]

/-- Back-reference emission: the fixed tables reproduce `compressFixedLoop`'s inline codes. -/
theorem emitToken_ref_eq (w : BitWriter) (len dist : Nat) (h3 : 3 ≤ len) (h258 : len ≤ 258) :
    emitToken fixedLitLenTable fixedDistTable w (.ref len dist)
      = (let t := cfLenTriple len
         let w := if t.1 ≤ 279 then writeBits w (reverseBits (t.1 - 256) 7) 7
                  else writeBits w (reverseBits (t.1 - 280 + 0xC0) 8) 8
         let w := if t.2.1 > 0 then writeBits w t.2.2 t.2.1 else w
         let d := encodeDistance dist
         let w := writeBits w (reverseBits d.1 5) 5
         if d.2.1 > 0 then writeBits w d.2.2 d.2.1 else w) := by
  obtain ⟨hlo, hhi, _, _, _, _⟩ := encodeLength_spec len (by omega) h3
  have hdc : (encodeDistance dist).1 ≤ 29 := encodeDistance_code_le_29 dist
  simp only [emitToken, emitHuffSymbol, cfLen_spec h3 h258,
    fixedLitCode_spec (by omega : (encodeLength len).1 < 288),
    fixedDistCode_spec (by omega : (encodeDistance dist).1 < 32)]
  simp only [if_neg (by omega : ¬((encodeLength len).1 ≤ 143)),
    if_neg (by omega : ¬((encodeLength len).1 ≤ 255))]
  by_cases h279 : (encodeLength len).1 ≤ 279
  · simp only [if_pos h279]
  · simp only [if_neg h279]



/-- Header + EOB framing. -/
theorem fixed_header_eq :
    writeBits (writeBits ({} : BitWriter) 1 1) 1 2 = writeBits ({} : BitWriter) 3 3 := by
  simp [writeBits, writeBits.flushBytes]

theorem emit_eob_eq (w : BitWriter) :
    emitHuffSymbol w fixedLitLenTable 256 = writeBits w 0 7 := by
  have h : fixedLitLenTable.codes[256]! = some (0, 7) := by
    rw [fixedLitCode_spec (by omega : 256 < 288)]; rfl
  have hr : reverseBits 0 7 = 0 := by simp [reverseBits]; decide
  simp [emitHuffSymbol, h, hr]

/-- Fusion: `compressFixed`'s single inline emit loop is exactly `tokenize` followed by a
    fold of `emitToken` over the fixed tables. -/
theorem tokenize_emit_eq (data : ByteArray) :
    ∀ fuel pos acc w,
      (tokenizeAux data fuel pos acc).foldl (emitToken fixedLitLenTable fixedDistTable) w
        = compressFixedLoop data fuel
            (acc.foldl (emitToken fixedLitLenTable fixedDistTable) w) pos := by
  intro fuel
  induction fuel with
  | zero => intro pos acc w; simp only [tokenizeAux, compressFixedLoop]
  | succ n ih =>
    intro pos acc w
    simp only [tokenizeAux, compressFixedLoop]
    by_cases hp : pos < data.size
    · simp only [if_pos hp]
      by_cases h3 : 3 ≤ (findLongestMatch data pos 32768 128).1
      · have hcond : (3 ≤ (findLongestMatch data pos 32768 128).1 ∧
            matchValid data pos (findLongestMatch data pos 32768 128).1
              (findLongestMatch data pos 32768 128).2 = true) :=
          ⟨h3, findLongestMatch_matchValid data pos h3⟩
        have h258 : (findLongestMatch data pos 32768 128).1 ≤ 258 :=
          (findLongestMatch_valid data pos h3).1
        rw [if_pos hcond, if_pos h3, ih]
        congr 1
        rw [Array.foldl_push, emitToken_ref_eq _ _ _ h3 h258]
        simp only [cfLenTriple]
        rfl
      · have hcond : ¬(3 ≤ (findLongestMatch data pos 32768 128).1 ∧
            matchValid data pos (findLongestMatch data pos 32768 128).1
              (findLongestMatch data pos 32768 128).2 = true) := fun h => h3 h.1
        rw [if_neg hcond, if_neg h3, ih]
        congr 1
        rw [Array.foldl_push, emitToken_lit_eq]
    · simp only [if_neg hp]

/-- **Law 12 connection theorem (PA16 L6/L7 bridge).** `compressFixed` -- the encoder
    `gzipCompress` actually calls, and the one the machine-code engines implement -- is
    extensionally the fixed-Huffman block built from `tokenize`, which every PA16 roundtrip
    theorem is stated about. Until this theorem existed, `compressFixed` and `compress` were
    unlinked twins and no zlib roundtrip theorem reached Spike 5. -/
theorem compressFixed_eq_emitFixedBlock (data : ByteArray) :
    compressFixed data = flushBitWriter (emitFixedBlock (tokenize data)) := by
  simp only [compressFixed, emitFixedBlock, emitTokens, tokenize, emit_eob_eq, fixed_header_eq]
  rw [tokenize_emit_eq data data.size 0 #[] (writeBits ({} : BitWriter) 3 3)]
  simp only [Array.foldl_empty]


/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- **What the connection theorem buys, universal over the input.** Composing it with
    `emitFixedBlock_roundtrip_soundness` (PA16 L7) gives DEFLATE roundtrip soundness for
    `compressFixed` itself -- the encoder `gzipCompress` calls and the machine-code engines
    implement. Before the connection theorem this statement was unreachable: every PA16
    roundtrip theorem was about `compress`/`emitFixedBlock`, a different function. -/
theorem compressFixed_roundtrip_soundness (data : ByteArray) :
    decompress (compressFixed data) = .ok data := by
  rw [compressFixed_eq_emitFixedBlock]
  exact emitFixedBlock_roundtrip_soundness data

end Grass.Std.Zlib.Deflate
