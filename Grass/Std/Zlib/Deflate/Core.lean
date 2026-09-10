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
import Grass.Std.Zlib.Deflate.Huffman

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Grass.Std.Zlib.Deflate

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Structured error taxonomy for DEFLATE / INFLATE operations. -/
inductive ZlibError where
  | unexpectedEof
  | invalidBlockType (btype : Nat)
  | invalidStoredBlockLengths
  | corruptedHuffmanTree
  | invalidDistanceCode (code : Nat)
  | invalidLengthCode (code : Nat)
  | custom (msg : String)
  deriving Repr, DecidableEq, Inhabited

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- LSB-first Bitstream Reader over a ByteArray. -/
structure BitReader where
  bytes    : ByteArray
  bytePos  : Nat := 0
  bitBuf   : UInt32 := 0
  bitCount : Nat := 0
  deriving Inhabited

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Initializes a BitReader from a ByteArray. -/
def mkBitReader (bytes : ByteArray) : BitReader :=
  { bytes := bytes, bytePos := 0, bitBuf := 0, bitCount := 0 }

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ensures at least `n` bits are available in the bit buffer (up to 24 bits). -/
def ensureBits (r : BitReader) (n : Nat) : BitReader :=
  let rec loop (cur : BitReader) : BitReader :=
    if cur.bitCount >= n || cur.bytePos >= cur.bytes.size then cur
    else
      let nextByte := cur.bytes.get! cur.bytePos
      let newBuf := (cur.bitBuf.toNat ||| (nextByte.toNat <<< cur.bitCount)).toUInt32
      loop { cur with bytePos := cur.bytePos + 1, bitBuf := newBuf, bitCount := cur.bitCount + 8 }
  termination_by cur.bytes.size - cur.bytePos
  decreasing_by simp_all; omega
  loop r

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Total number of unconsumed bits remaining in a `BitReader`: bits already buffered
    plus 8 bits for every unread byte. This is the natural termination measure for any
    loop that consumes bits from a `BitReader` via `readBits`/`decodeHuffmanSymbol`. -/
def remainingBits (r : BitReader) : Nat :=
  r.bitCount + 8 * (r.bytes.size - r.bytePos)

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `ensureBits.loop` only moves bits from the unread byte suffix into the bit buffer;
    it never consumes or fabricates bits, so `remainingBits` is invariant. Proved via
    `ensureBits.loop`'s own `.induct` principle, available now that `ensureBits` is
    well-founded rather than `partial` (its equation lemma makes this statable at all). -/
theorem ensureBits_loop_remainingBits (n : Nat) (cur : BitReader) :
    remainingBits (ensureBits.loop n cur) = remainingBits cur := by
  induction cur using ensureBits.loop.induct (n := n) with
  | case1 x hx => rw [ensureBits.loop.eq_1, if_pos hx]
  | case2 x hx nextByte newBuf ih =>
    rw [ensureBits.loop.eq_1, if_neg hx, ih]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hx
    simp only [remainingBits]
    omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `ensureBits` (the top-level wrapper) preserves `remainingBits`. -/
theorem ensureBits_remainingBits (r : BitReader) (n : Nat) :
    remainingBits (ensureBits r n) = remainingBits r := by
  rw [ensureBits.eq_1]
  exact ensureBits_loop_remainingBits n r

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Reads `n` bits (LSB-first) from the bitstream. -/
def readBits (r : BitReader) (n : Nat) : Except ZlibError (BitReader × Nat) :=
  let r' := ensureBits r n
  if r'.bitCount < n then .error .unexpectedEof
  else
    let mask := (1 <<< n) - 1
    let val := (r'.bitBuf.toNat &&& mask)
    let newBuf := (r'.bitBuf.toNat >>> n).toUInt32
    let newCount := r'.bitCount - n
    .ok ({ r' with bitBuf := newBuf, bitCount := newCount }, val)

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- A successful `readBits r n` consumes exactly `n` bits: `remainingBits` drops by `n`.
    This is the "successful `readBits` strictly shrinks the measure" fact needed to
    justify well-founded recursion over any loop that decodes a `BitReader` stream. -/
theorem readBits_remainingBits (r : BitReader) (n : Nat) (rOut : BitReader) (v : Nat)
    (hok : readBits r n = .ok (rOut, v)) :
    remainingBits rOut + n = remainingBits r := by
  have heq : remainingBits (ensureBits r n) = remainingBits r := ensureBits_remainingBits r n
  unfold readBits at hok
  dsimp only at hok
  split at hok
  · simp at hok
  · rename_i hge
    obtain ⟨hok1, _⟩ := Prod.mk.injEq .. |>.mp (Except.ok.injEq .. |>.mp hok)
    simp only [remainingBits] at heq ⊢
    have hbc : rOut.bitCount = (ensureBits r n).bitCount - n := by rw [← hok1]
    have hbp : rOut.bytePos = (ensureBits r n).bytePos := by rw [← hok1]
    have hbs : rOut.bytes.size = (ensureBits r n).bytes.size := by rw [← hok1]
    omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Drops remaining bits in the current byte, byte-aligning the reader. -/
def alignToByte (r : BitReader) : BitReader :=
  { r with bitBuf := 0, bitCount := 0 }

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Decodes a single Huffman symbol from the bitstream using a decode tree. -/
def decodeHuffmanSymbol (r : BitReader) (tree : HuffmanTable) : Except ZlibError (BitReader × Nat) :=
  let rec step (curR : BitReader) (node : HuffmanNode) : Except ZlibError (BitReader × Nat) :=
    match node with
    | HuffmanNode.leaf sym => .ok (curR, sym)
    | HuffmanNode.branch l rOpt =>
      match readBits curR 1 with
      | .error e => .error e
      | .ok (nextR, bit) =>
        if bit == 0 then
          match l with
          | some n => step nextR n
          | none => .error .corruptedHuffmanTree
        else
          match rOpt with
          | some n => step nextR n
          | none => .error .corruptedHuffmanTree
  termination_by node
  decreasing_by all_goals simp_all; omega
  step r tree.root

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- A successful `decodeHuffmanSymbol.step` call never *fabricates* bits: the reader it returns
    has never consumed more of the stream than it started with. True for every `HuffmanNode`,
    including a bare `leaf` (0 bits consumed) -- this is the non-strict half of the fact
    `decodeHuffmanStream`/`decompress` need for their termination measure; the strict half
    (`decodeHuffmanSymbol_remainingBits_lt` below) additionally requires the tree's *root* to
    be a `branch`. -/
theorem decodeHuffmanSymbol_step_remainingBits_le (curR : BitReader) (node : HuffmanNode) :
    ∀ (nextR : BitReader) (sym : Nat),
      decodeHuffmanSymbol.step curR node = .ok (nextR, sym) →
      remainingBits nextR ≤ remainingBits curR := by
  induction curR, node using decodeHuffmanSymbol.step.induct with
  | case1 curR sym' =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def] at hok
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨h1, _⟩ := hok
    rw [h1]
    exact Nat.le_refl _
  | case2 curR l rOpt e he =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, he] at hok
    simp at hok
  | case3 curR rOpt nextR' bit hread hbit n ih =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, hread] at hok
    simp only [hbit, if_true] at hok
    have hle := ih nextR sym hok
    have heq := readBits_remainingBits curR 1 nextR' bit hread
    omega
  | case4 curR rOpt nextR' bit hread hbit =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, hread] at hok
    simp [hbit] at hok
  | case5 curR l nextR' bit hread hbit n ih =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, hread] at hok
    simp only [hbit] at hok
    have hle := ih nextR sym hok
    have heq := readBits_remainingBits curR 1 nextR' bit hread
    omega
  | case6 curR l nextR' bit hread hbit =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, hread] at hok
    simp [hbit] at hok

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- **The termination fact `decodeHuffmanStream`/`decompress` need**: given a `branch`-rooted
    decode tree, a successful `decodeHuffmanSymbol` call strictly shrinks `remainingBits` --
    the root's `branch` case unconditionally reads (and, on success, consumes) 1 bit via
    `readBits curR 1` before any recursive descent, and `decodeHuffmanSymbol_step_remainingBits_le`
    shows the descent below that first read can only consume further bits, never give them back.
    Every `HuffmanTable` this codebase ever constructs satisfies the hypothesis unconditionally
    (`buildHuffmanTable_isBranch`, `Stdlib/Zlib/Huffman.lean`), so this closes the termination
    obligation Lean could not previously discharge for the general `HuffmanTable` type. -/
theorem decodeHuffmanSymbol_remainingBits_lt (r : BitReader) (tree : HuffmanTable)
    (hroot : ∃ l rr, tree.root = HuffmanNode.branch l rr) (nextR : BitReader) (sym : Nat)
    (hok : decodeHuffmanSymbol r tree = .ok (nextR, sym)) :
    remainingBits nextR < remainingBits r := by
  obtain ⟨l, rr, hr⟩ := hroot
  unfold decodeHuffmanSymbol at hok
  rw [hr, decodeHuffmanSymbol.step.eq_def] at hok
  cases hread : readBits r 1 with
  | error e => rw [hread] at hok; simp at hok
  | ok val =>
    obtain ⟨nextR', bit⟩ := val
    rw [hread] at hok
    by_cases hbit : (bit == 0) = true
    · simp only [hbit, if_true] at hok
      cases l with
      | none => simp at hok
      | some n =>
        simp only at hok
        have hle := decodeHuffmanSymbol_step_remainingBits_le nextR' n nextR sym hok
        have heq := readBits_remainingBits r 1 nextR' bit hread
        omega
    · simp only [hbit] at hok
      cases rr with
      | none => simp at hok
      | some n =>
        simp only at hok
        have hle := decodeHuffmanSymbol_step_remainingBits_le nextR' n nextR sym hok
        have heq := readBits_remainingBits r 1 nextR' bit hread
        omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Non-strict, hypothesis-free companion to `decodeHuffmanSymbol_remainingBits_lt`: a
    successful `decodeHuffmanSymbol` call never fabricates bits, for *any* tree (leaf-rooted
    included). Used where the decoded symbol's own reader isn't the one driving termination
    (`decodeHuffmanStream`'s distance-symbol decode: the literal/length symbol earlier in the
    same iteration already supplies the strict decrease). -/
theorem decodeHuffmanSymbol_remainingBits_le (r : BitReader) (tree : HuffmanTable)
    (nextR : BitReader) (sym : Nat) (hok : decodeHuffmanSymbol r tree = .ok (nextR, sym)) :
    remainingBits nextR ≤ remainingBits r := by
  unfold decodeHuffmanSymbol at hok
  exact decodeHuffmanSymbol_step_remainingBits_le r tree.root nextR sym hok

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `decodeHuffmanStream`'s extra-bits reads are each guarded by `if n > 0 then readBits r n
    else pure (r, 0)` (RFC 1951 §3.2.5's zero-extra-bit length/distance codes read nothing);
    either way, on success, the reader never gains bits back. -/
theorem maybeReadBits_remainingBits_le (r : BitReader) (n : Nat) (rOut : BitReader) (v : Nat)
    (hok : (if n > 0 then readBits r n else pure (r, 0)) = .ok (rOut, v)) :
    remainingBits rOut ≤ remainingBits r := by
  split at hok
  · rename_i hpos
    have := readBits_remainingBits r n rOut v hok
    omega
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hok
    rw [← hok.1]
    exact Nat.le_refl _

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- LSB-first Bitstream Writer accumulating bytes. -/
structure BitWriter where
  bytes    : ByteArray := ByteArray.empty
  bitBuf   : UInt32 := 0
  bitCount : Nat := 0
  deriving Inhabited

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Writes `n` bits (LSB-first) into the bitstream. -/
def writeBits (w : BitWriter) (value : Nat) (n : Nat) : BitWriter :=
  let newBuf := (w.bitBuf.toNat ||| (value <<< w.bitCount)).toUInt32
  let newCount := w.bitCount + n
  let rec flushBytes (buf : UInt32) (cnt : Nat) (acc : ByteArray) : (UInt32 × Nat × ByteArray) :=
    if cnt >= 8 then
      let byteVal := (buf.toNat &&& 0xFF).toUInt8
      flushBytes ((buf.toNat >>> 8).toUInt32) (cnt - 8) (acc.push byteVal)
    else (buf, cnt, acc)
  let (finalBuf, finalCount, finalBytes) := flushBytes newBuf newCount w.bytes
  { bytes := finalBytes, bitBuf := finalBuf, bitCount := finalCount }

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Flushes any pending bits and byte-aligns the output. -/
def flushBitWriter (w : BitWriter) : ByteArray :=
  if w.bitCount > 0 then
    let byteVal := (w.bitBuf.toNat &&& 0xFF).toUInt8
    w.bytes.push byteVal
  else w.bytes

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- RFC 1951 Length base values and extra bits (codes 257–285). -/
def lengthTable : Array (Nat × Nat) := #[
  (3, 0),   (4, 0),   (5, 0),   (6, 0),   (7, 0),   (8, 0),   (9, 0),   (10, 0),
  (11, 1),  (13, 1),  (15, 1),  (17, 1),
  (19, 2),  (23, 2),  (27, 2),  (31, 2),
  (35, 3),  (43, 3),  (51, 3),  (59, 3),
  (67, 4),  (83, 4),  (99, 4),  (115, 4),
  (131, 5), (163, 5), (195, 5), (227, 5),
  (258, 0)
]

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- RFC 1951 Distance base values and extra bits (codes 0–29). -/
def distanceTable : Array (Nat × Nat) := #[
  (1, 0),     (2, 0),     (3, 0),     (4, 0),
  (5, 1),     (7, 1),     (9, 2),     (13, 2),
  (17, 3),    (25, 3),    (33, 4),    (49, 4),
  (65, 5),    (97, 5),    (129, 6),   (193, 6),
  (257, 7),   (385, 7),   (513, 8),   (769, 8),
  (1025, 9),  (1537, 9),  (2049, 10), (3073, 10),
  (4097, 11), (6145, 11), (8193, 12), (12289, 12),
  (16385, 13), (24577, 13)
]

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Permutation order for Dynamic Huffman code length alphabet (RFC 1951 §3.2.7). -/
def clenOrder : Array Nat := #[
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes an uncompressed stored block (BTYPE = 00). -/
def decodeStoredBlock (r : BitReader) (out : ByteArray) : Except ZlibError (BitReader × ByteArray) :=
  let rAligned := alignToByte r
  if rAligned.bytePos + 4 > rAligned.bytes.size then .error .unexpectedEof
  else
    let len0 := (rAligned.bytes.get! rAligned.bytePos).toNat
    let len1 := (rAligned.bytes.get! (rAligned.bytePos + 1)).toNat
    let nlen0 := (rAligned.bytes.get! (rAligned.bytePos + 2)).toNat
    let nlen1 := (rAligned.bytes.get! (rAligned.bytePos + 3)).toNat
    let len := len0 ||| (len1 <<< 8)
    let nlen := nlen0 ||| (nlen1 <<< 8)
    if (len ^^^ 0xFFFF) != nlen then .error .invalidStoredBlockLengths
    else
      let start := rAligned.bytePos + 4
      if start + len > rAligned.bytes.size then .error .unexpectedEof
      else
        let newOut := Id.run do
          let mut acc := out
          for i in [0:len] do
            acc := acc.push (rAligned.bytes.get! (start + i))
          acc
        .ok ({ rAligned with bytePos := start + len }, newOut)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A successful `decodeStoredBlock` call never fabricates bits: byte-aligning only drops
    (never adds) buffered bits, and the stored payload only advances `bytePos` forward. -/
theorem decodeStoredBlock_remainingBits_le (r : BitReader) (out : ByteArray) (rOut : BitReader)
    (outOut : ByteArray) (hok : decodeStoredBlock r out = .ok (rOut, outOut)) :
    remainingBits rOut ≤ remainingBits r := by
  unfold decodeStoredBlock at hok
  dsimp only at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hrOut, _⟩ := hok
    rw [← hrOut]
    simp only [remainingBits, alignToByte]
    omega

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes LZ77 literals and match back-references using literal and distance Huffman tables.
    Requires both tables to be `branch`-rooted (`hLit`/`hDist`) -- the invariant
    `buildHuffmanTable_isBranch` (`Stdlib/Zlib/Huffman.lean`) establishes *unconditionally*, for
    every table this codebase ever constructs (fixed or dynamic, well-formed or adversarial), so
    neither caller (`decompress`, below) needs to validate anything beyond calling
    `buildHuffmanTable` to satisfy these hypotheses.

    Well-founded on `remainingBits curR`: `decodeHuffmanSymbol_remainingBits_lt` (via `hLit`)
    guarantees the literal/length symbol decode alone strictly shrinks the measure on every
    iteration that doesn't terminate (the RFC 1951 §3.2.5/§3.2.6 fact motivating this file's
    invariant design: a canonical Huffman code has no zero-length codeword, so decoding a symbol
    from a genuine, `branch`-rooted table always consumes at least 1 bit). `hDist` is threaded
    for signature symmetry with `hLit` -- both tables are always supplied together, from the
    same `buildHuffmanTable` call sites -- but is not itself load-bearing for *this* termination
    argument: the distance-symbol decode and both extra-bits reads only need the unconditional,
    hypothesis-free `≤` facts (`decodeHuffmanSymbol_remainingBits_le`,
    `maybeReadBits_remainingBits_le`), since the literal/length decode's strict decrease alone
    already dominates the chain. -/
def decodeHuffmanStream (r : BitReader) (litTable distTable : HuffmanTable)
    (hLit : ∃ l rr, litTable.root = HuffmanNode.branch l rr)
    (hDist : ∃ l rr, distTable.root = HuffmanNode.branch l rr)
    (out : ByteArray) : Except ZlibError (BitReader × ByteArray) :=
  let rec go (curR : BitReader) (curOut : ByteArray)
      (hL : ∃ l rr, litTable.root = HuffmanNode.branch l rr)
      (hD : ∃ l rr, distTable.root = HuffmanNode.branch l rr) :
      Except ZlibError (BitReader × ByteArray) :=
    match hsym : decodeHuffmanSymbol curR litTable with
    | .error e => .error e
    | .ok (nextR, sym) =>
      if sym < 256 then
        go nextR (curOut.push sym.toUInt8) hL hD
      else if sym == 256 then
        .ok (nextR, curOut)
      else if sym <= 285 then
        let lenIdx := sym - 257
        let (baseLen, extraBits) := lengthTable[lenIdx]!
        match hlen : (if extraBits > 0 then readBits nextR extraBits else pure (nextR, 0)) with
        | .error e => .error e
        | .ok (rLen, extraVal) =>
          let matchLen := baseLen + extraVal
          match hdsym : decodeHuffmanSymbol rLen distTable with
          | .error e => .error e
          | .ok (rDistSym, distSym) =>
            if distSym >= 30 then .error (.invalidDistanceCode distSym)
            else
              let (baseDist, distExtraBits) := distanceTable[distSym]!
              match hdext : (if distExtraBits > 0 then readBits rDistSym distExtraBits else pure (rDistSym, 0)) with
              | .error e => .error e
              | .ok (rDist, distExtraVal) =>
                let matchDist := baseDist + distExtraVal
                if matchDist == 0 || matchDist > curOut.size then
                  .error (.custom s!"Invalid back-reference distance {matchDist} on output size {curOut.size}")
                else
                  let newOut := Id.run do
                    let mut acc := curOut
                    for _ in [0:matchLen] do
                      let srcIdx := acc.size - matchDist
                      acc := acc.push (acc.get! srcIdx)
                    acc
                  go rDist newOut hL hD
      else
        .error (.invalidLengthCode sym)
  termination_by remainingBits curR
  decreasing_by
    · exact decodeHuffmanSymbol_remainingBits_lt curR litTable hL nextR sym hsym
    · have h1 := decodeHuffmanSymbol_remainingBits_lt curR litTable hL nextR sym hsym
      have h2 := maybeReadBits_remainingBits_le nextR extraBits rLen extraVal hlen
      have h3 := decodeHuffmanSymbol_remainingBits_le rLen distTable rDistSym distSym hdsym
      have h4 := maybeReadBits_remainingBits_le rDistSym distExtraBits rDist distExtraVal hdext
      omega
  go r out hLit hDist

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeHuffmanStream`'s internal loop (`go`) never fabricates bits: a successful call
    returns a reader that has consumed no more of the stream than it started with. Strong
    induction on `remainingBits curR` rather than `go.induct`, since `go`'s own well-founded
    recursion is already on that same measure -- every recursive call in `go`'s body already
    comes with a proof (`decodeHuffmanSymbol_remainingBits_lt`/`_le`,
    `maybeReadBits_remainingBits_le`) that `remainingBits` only shrinks, so the outer induction
    just needs to track that shrinkage to justify recursing. This is the fact `decompress`
    needs to bound the whole-block effect of a fixed- or dynamic-Huffman block, not just one
    symbol. -/
theorem decodeHuffmanStream_go_remainingBits_le (litTable distTable : HuffmanTable)
    (hL : ∃ l rr, litTable.root = HuffmanNode.branch l rr)
    (hD : ∃ l rr, distTable.root = HuffmanNode.branch l rr) :
    ∀ (curR : BitReader) (curOut : ByteArray) (nextR : BitReader) (outOut : ByteArray),
      decodeHuffmanStream.go litTable distTable curR curOut hL hD = .ok (nextR, outOut) →
      remainingBits nextR ≤ remainingBits curR := by
  have main : ∀ n, ∀ curR : BitReader, remainingBits curR = n → ∀ (curOut : ByteArray)
      (nextR : BitReader) (outOut : ByteArray),
      decodeHuffmanStream.go litTable distTable curR curOut hL hD = .ok (nextR, outOut) →
      remainingBits nextR ≤ remainingBits curR := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro curR hn curOut nextR outOut hok
      rw [decodeHuffmanStream.go.eq_def] at hok
      dsimp only at hok
      cases hsym : decodeHuffmanSymbol curR litTable with
      | error e => rw [hsym] at hok; dsimp only at hok; simp at hok
      | ok val =>
        obtain ⟨nextR', sym⟩ := val
        rw [hsym] at hok
        dsimp only at hok
        split at hok
        · -- sym < 256, recurse
          have hlt := decodeHuffmanSymbol_remainingBits_lt curR litTable hL nextR' sym hsym
          have hres := ih (remainingBits nextR') (by omega) nextR' rfl (curOut.push sym.toUInt8) nextR outOut hok
          omega
        · split at hok
          · -- sym == 256, terminal
            simp only [Except.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨h1, _⟩ := hok
            rw [← h1]
            exact decodeHuffmanSymbol_remainingBits_le curR litTable nextR' sym hsym
          · split at hok
            · -- sym ≤ 285
              cases hlen : (if lengthTable[sym - 257]!.2 > 0 then readBits nextR' lengthTable[sym - 257]!.2
                  else pure (nextR', 0)) with
              | error e => rw [hlen] at hok; dsimp only at hok; simp at hok
              | ok val2 =>
                obtain ⟨rLen, extraVal⟩ := val2
                rw [hlen] at hok
                dsimp only at hok
                cases hdsym : decodeHuffmanSymbol rLen distTable with
                | error e => rw [hdsym] at hok; dsimp only at hok; simp at hok
                | ok val3 =>
                  obtain ⟨rDistSym, distSym⟩ := val3
                  rw [hdsym] at hok
                  dsimp only at hok
                  split at hok
                  · -- distSym ≥ 30, error
                    simp at hok
                  · cases hdext : (if distanceTable[distSym]!.2 > 0
                        then readBits rDistSym distanceTable[distSym]!.2 else pure (rDistSym, 0)) with
                    | error e => rw [hdext] at hok; dsimp only at hok; simp at hok
                    | ok val4 =>
                      obtain ⟨rDist, distExtraVal⟩ := val4
                      rw [hdext] at hok
                      dsimp only at hok
                      split at hok
                      · -- invalid match distance, error
                        simp at hok
                      · -- success, recurse
                        have h1 := decodeHuffmanSymbol_remainingBits_lt curR litTable hL nextR' sym hsym
                        have h2 := maybeReadBits_remainingBits_le nextR' lengthTable[sym - 257]!.2 rLen extraVal hlen
                        have h3 := decodeHuffmanSymbol_remainingBits_le rLen distTable rDistSym distSym hdsym
                        have h4 := maybeReadBits_remainingBits_le rDistSym distanceTable[distSym]!.2 rDist
                          distExtraVal hdext
                        have hres := ih (remainingBits rDist) (by omega) rDist rfl _ nextR outOut hok
                        omega
            · -- sym > 285, error
              simp at hok
  intro curR curOut nextR outOut hok
  exact main (remainingBits curR) curR rfl curOut nextR outOut hok

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeHuffmanStream` never fabricates bits: a successful call's output reader has
    consumed no more of the stream than the input reader offered. Thin wrapper around
    `decodeHuffmanStream_go_remainingBits_le` (`go` is called with `curR := r`, `curOut := out`
    at the top). This is the whole-block bound `decompress`'s outer loop needs, mirroring
    `decodeStoredBlock_remainingBits_le` for the other two block kinds. -/
theorem decodeHuffmanStream_remainingBits_le (r : BitReader) (litTable distTable : HuffmanTable)
    (hLit : ∃ l rr, litTable.root = HuffmanNode.branch l rr)
    (hDist : ∃ l rr, distTable.root = HuffmanNode.branch l rr) (out : ByteArray)
    (nextR : BitReader) (nextOut : ByteArray)
    (hok : decodeHuffmanStream r litTable distTable hLit hDist out = .ok (nextR, nextOut)) :
    remainingBits nextR ≤ remainingBits r := by
  unfold decodeHuffmanStream at hok
  exact decodeHuffmanStream_go_remainingBits_le litTable distTable hLit hDist r out nextR nextOut hok

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Pushes `n` copies of `val` onto the end of `arr` (equivalent to the imperative
    `for _ in [0:n] do arr := arr.push val`, expressed as structural recursion on `n`
    so its `.size` effect is provable by induction). -/
def pushRepeated (arr : Array Nat) (val : Nat) (n : Nat) : Array Nat :=
  match n with
  | 0 => arr
  | n + 1 => pushRepeated (arr.push val) val n

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `pushRepeated` grows the array by exactly `n` elements. -/
theorem pushRepeated_size (arr : Array Nat) (val n : Nat) :
    (pushRepeated arr val n).size = arr.size + n := by
  induction n generalizing arr with
  | zero => simp [pushRepeated]
  | succ n ih => simp [pushRepeated, ih, Array.size_push]; omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Reads `hclen` 3-bit code lengths for the code-length alphabet (RFC 1951 §3.2.7), placing
    each at its `clenOrder` permutation position. Structural recursion on `fuel` (remaining
    codes to read) rather than a `for`/monadic-`forIn` loop, so its bits-consumed effect is
    provable by induction -- see `decodeClenArray_remainingBits_le`. Called with `fuel := hclen`,
    `pos := 0`, this is exactly `decodeDynamicTables`'s original `for i in [0:hclen]` loop. -/
def decodeClenArray (hclen : Nat) : Nat → Nat → BitReader → Array Nat →
    Except ZlibError (BitReader × Array Nat)
  | 0, _pos, curR, clenArr => .ok (curR, clenArr)
  | fuel + 1, pos, curR, clenArr =>
    match readBits curR 3 with
    | .error e => .error e
    | .ok (nextR, bitLen) =>
      decodeClenArray hclen fuel (pos + 1) nextR (clenArr.set! clenOrder[pos]! bitLen)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeClenArray` never fabricates bits: on success, the reader it returns has consumed
    only from the one it started with. Structural induction on `fuel`, unlike the well-founded
    inductions above -- `decodeClenArray` recurses on `fuel` directly, not on a measure derived
    from the `BitReader`. -/
theorem decodeClenArray_remainingBits_le (hclen : Nat) :
    ∀ (fuel pos : Nat) (curR : BitReader) (clenArr : Array Nat) (rOut : BitReader) (arrOut : Array Nat),
      decodeClenArray hclen fuel pos curR clenArr = .ok (rOut, arrOut) →
      remainingBits rOut ≤ remainingBits curR := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos curR clenArr rOut arrOut hok
    simp only [decodeClenArray, Except.ok.injEq, Prod.mk.injEq] at hok
    rw [← hok.1]
    exact Nat.le_refl _
  | succ fuel ih =>
    intro pos curR clenArr rOut arrOut hok
    rw [decodeClenArray] at hok
    cases hread : readBits curR 3 with
    | error e => rw [hread] at hok; simp at hok
    | ok val =>
      obtain ⟨nextR, bitLen⟩ := val
      rw [hread] at hok
      simp only at hok
      have h1 := ih (pos + 1) nextR (clenArr.set! clenOrder[pos]! bitLen) rOut arrOut hok
      have h2 := readBits_remainingBits curR 3 nextR bitLen hread
      omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes a dynamic Huffman block header (BTYPE = 10) and returns the constructed tables. -/
def decodeDynamicTables (r : BitReader) : Except ZlibError (BitReader × HuffmanTable × HuffmanTable) := do
  let (r1, hlitVal) ← readBits r 5
  let (r2, hdistVal) ← readBits r1 5
  let (r3, hclenVal) ← readBits r2 4
  let hlit := hlitVal + 257
  let hdist := hdistVal + 1
  let hclen := hclenVal + 4

  let (curR, clenArr) ← decodeClenArray hclen hclen 0 r3 (Array.replicate 19 0)
  let clenTable := buildHuffmanTable clenArr 7

  let totalLengths := hlit + hdist
  let rec go (br : BitReader) (lengths : Array Nat) :
      Except ZlibError (BitReader × Array Nat) :=
    if lengths.size < totalLengths then
      match decodeHuffmanSymbol br clenTable with
      | .error e => .error e
      | .ok (nextR, sym) =>
        if sym <= 15 then
          go nextR (lengths.push sym)
        else if sym == 16 then
          if lengths.isEmpty then .error .corruptedHuffmanTree
          else
            let lastVal := lengths[lengths.size - 1]!
            match readBits nextR 2 with
            | .error e => .error e
            | .ok (rRepeat, extra) =>
              go rRepeat (pushRepeated lengths lastVal (extra + 3))
        else if sym == 17 then
          match readBits nextR 3 with
          | .error e => .error e
          | .ok (rRepeat, extra) =>
            go rRepeat (pushRepeated lengths 0 (extra + 3))
        else if sym == 18 then
          match readBits nextR 7 with
          | .error e => .error e
          | .ok (rRepeat, extra) =>
            go rRepeat (pushRepeated lengths 0 (extra + 11))
        else
          .error .corruptedHuffmanTree
    else .ok (br, lengths)
  termination_by totalLengths - lengths.size
  decreasing_by
    all_goals simp_all [pushRepeated_size]
    all_goals omega

  let (finalR, lengths) ← go curR (Array.mkEmpty totalLengths)

  let litLengths := lengths.extract 0 hlit
  let distLengths := lengths.extract hlit totalLengths
  let litTable := buildHuffmanTable litLengths 15
  let distTable := buildHuffmanTable distLengths 15
  .ok (finalR, litTable, distTable)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeDynamicTables`'s internal code-length-parsing loop (`go`) never fabricates bits.
    Induction on `go`'s own well-founded recursion (`totalLengths - lengths.size`, from P0) --
    a different measure than the one this lemma proves a fact *about* (`remainingBits`); each
    step only reads via `decodeHuffmanSymbol`/`readBits`, both bits-only-consuming. -/
theorem decodeDynamicTables_go_remainingBits_le (clenTable : HuffmanTable) (totalLengths : Nat) :
    ∀ (br : BitReader) (lengths : Array Nat) (nextR : BitReader) (lengths' : Array Nat),
      decodeDynamicTables.go clenTable totalLengths br lengths = .ok (nextR, lengths') →
      remainingBits nextR ≤ remainingBits br := by
  intro br lengths
  induction br, lengths using decodeDynamicTables.go.induct (clenTable := clenTable) (totalLengths := totalLengths) with
  | case1 br lengths hlt e he =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, he] at hok
    simp at hok
  | case2 br lengths hlt nextR' bit hsym hle ih =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp only [hle, if_true] at hok
    have h1 := ih nextR lengths' hok
    have h2 := decodeHuffmanSymbol_remainingBits_le br clenTable nextR' bit hsym
    omega
  | case3 br lengths hlt nextR' bit hsym hgt h16 hempty =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, hempty] at hok
  | case4 br lengths hlt nextR' bit hsym hgt h16 hne e he =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, hne, he] at hok
  | case5 br lengths hlt nextR' bit hsym hgt h16 hne lastVal nextR'' extra hread ih =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp only [hgt, h16, hne, if_false, if_true, hread] at hok
    have h1 := ih nextR lengths' hok
    have h2 := decodeHuffmanSymbol_remainingBits_le br clenTable nextR' bit hsym
    have h3 := readBits_remainingBits nextR' 2 nextR'' extra hread
    omega
  | case6 br lengths hlt nextR' bit hsym hgt h16 h17 e he =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, h17, he] at hok
  | case7 br lengths hlt nextR' bit hsym hgt h16 h17 nextR'' extra hread ih =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp only [hgt, h16, h17, if_false, if_true, hread] at hok
    have h1 := ih nextR lengths' hok
    have h2 := decodeHuffmanSymbol_remainingBits_le br clenTable nextR' bit hsym
    have h3 := readBits_remainingBits nextR' 3 nextR'' extra hread
    omega
  | case8 br lengths hlt nextR' bit hsym hgt h16 h17 h18 e he =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, h17, h18, he] at hok
  | case9 br lengths hlt nextR' bit hsym hgt h16 h17 h18 nextR'' extra hread ih =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp only [hgt, h16, h17, h18, if_false, if_true, hread] at hok
    have h1 := ih nextR lengths' hok
    have h2 := decodeHuffmanSymbol_remainingBits_le br clenTable nextR' bit hsym
    have h3 := readBits_remainingBits nextR' 7 nextR'' extra hread
    omega
  | case10 br lengths hlt nextR' bit hsym hgt h16 h17 h18 =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, h17, h18] at hok
  | case11 br lengths hge =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_neg hge] at hok
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    rw [← hok.1]
    exact Nat.le_refl _

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Bridges a successful `decodeDynamicTables` call to the two facts `decompress` needs about
    its output: the reader only shrinks (`decodeDynamicTables_go_remainingBits_le` composed with
    three exact `readBits_remainingBits` reads and `decodeClenArray_remainingBits_le`), and both
    tables are literally `buildHuffmanTable` applications -- so `buildHuffmanTable_isBranch`
    (`Stdlib/Zlib/Huffman.lean`) applies to them unconditionally, exactly as it does to the fixed
    tables, regardless of how the transmitted code lengths were chosen. -/
theorem decodeDynamicTables_bridge (r : BitReader) (rOut : BitReader) (litTbl distTbl : HuffmanTable)
    (hok : decodeDynamicTables r = .ok (rOut, litTbl, distTbl)) :
    remainingBits rOut ≤ remainingBits r ∧
    ∃ litLengths distLengths, litTbl = buildHuffmanTable litLengths 15 ∧
      distTbl = buildHuffmanTable distLengths 15 := by
  unfold decodeDynamicTables at hok
  cases h1 : readBits r 5 with
  | error e => rw [h1] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
  | ok val1 =>
    obtain ⟨r1, hlitVal⟩ := val1
    rw [h1] at hok
    simp only [Bind.bind, Except.bind] at hok
    cases h2 : readBits r1 5 with
    | error e => rw [h2] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
    | ok val2 =>
      obtain ⟨r2, hdistVal⟩ := val2
      rw [h2] at hok
      simp only [Bind.bind, Except.bind] at hok
      cases h3 : readBits r2 4 with
      | error e => rw [h3] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
      | ok val3 =>
        obtain ⟨r3, hclenVal⟩ := val3
        rw [h3] at hok
        simp only [Bind.bind, Except.bind] at hok
        cases h4 : decodeClenArray (hclenVal + 4) (hclenVal + 4) 0 r3 (Array.replicate 19 0) with
        | error e => rw [h4] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
        | ok val4 =>
          obtain ⟨curR, clenArr⟩ := val4
          rw [h4] at hok
          simp only [Bind.bind, Except.bind] at hok
          cases h5 : decodeDynamicTables.go (buildHuffmanTable clenArr 7)
              (hlitVal + 257 + (hdistVal + 1)) curR (Array.mkEmpty (hlitVal + 257 + (hdistVal + 1))) with
          | error e => rw [h5] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
          | ok val5 =>
            obtain ⟨finalR, lengths⟩ := val5
            rw [h5] at hok
            simp only [Bind.bind, Except.bind] at hok
            simp only [Except.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨hrOut, hlitTbl, hdistTbl⟩ := hok
            refine ⟨?_, lengths.extract 0 (hlitVal + 257),
                lengths.extract (hlitVal + 257) (hlitVal + 257 + (hdistVal + 1)),
                hlitTbl.symm, hdistTbl.symm⟩
            have g1 := readBits_remainingBits r 5 r1 hlitVal h1
            have g2 := readBits_remainingBits r1 5 r2 hdistVal h2
            have g3 := readBits_remainingBits r2 4 r3 hclenVal h3
            have g4 := decodeClenArray_remainingBits_le (hclenVal + 4) (hclenVal + 4) 0 r3
              (Array.replicate 19 0) curR clenArr h4
            have g5 := decodeDynamicTables_go_remainingBits_le (buildHuffmanTable clenArr 7)
              (hlitVal + 257 + (hdistVal + 1)) curR (Array.mkEmpty (hlitVal + 257 + (hdistVal + 1)))
              finalR lengths h5
            rw [← hrOut]
            omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Bridges a successful `decodeDynamicTables` call directly to the `branch`-rootedness
    invariant `decompress` needs to call `decodeHuffmanStream` with -- without ever
    pattern-matching on `decodeDynamicTables_bridge`'s existential witness itself (which would
    require eliminating a `Prop` into `decompress`'s `Except ZlibError ByteArray` result type,
    not generally legal). Both conjuncts here are themselves `Prop`s, so this theorem's
    *statement* already is the exact fact `decompress` needs to hand to `decodeHuffmanStream`
    as `hLit`/`hDist`: no witness data ever needs to leave `Prop` land. -/
theorem decodeDynamicTables_isBranch (r rOut : BitReader) (litTbl distTbl : HuffmanTable)
    (hok : decodeDynamicTables r = .ok (rOut, litTbl, distTbl)) :
    (∃ l rr, litTbl.root = HuffmanNode.branch l rr) ∧
    (∃ l rr, distTbl.root = HuffmanNode.branch l rr) := by
  obtain ⟨_, litLengths, distLengths, hlit, hdist⟩ := decodeDynamicTables_bridge r rOut litTbl distTbl hok
  exact ⟨hlit ▸ buildHuffmanTable_isBranch litLengths 15, hdist ▸ buildHuffmanTable_isBranch distLengths 15⟩

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Core RFC 1951 INFLATE decompressor. Well-founded on `remainingBits curR`: every iteration
    reads a 3-bit block header (`bfinal` then `btype`, exactly 3 bits via two `readBits` calls
    -- that's where the strict decrease comes from) and then dispatches on `btype` to one of
    the three block-body decoders. Each is proven to only shrink (never grow) `remainingBits`:
    `decodeStoredBlock_remainingBits_le` for BTYPE=00, `decodeHuffmanStream_remainingBits_le`
    (fed the fixed tables' unconditional `buildHuffmanTable_isBranch` witnesses) for BTYPE=01,
    and the same lemma fed `decodeDynamicTables_isBranch`'s witnesses -- composed with
    `decodeDynamicTables_bridge`'s bound on the table-header prefix -- for BTYPE=10. Since
    `buildHuffmanTable_isBranch` (`Stdlib/Zlib/Huffman.lean`) holds unconditionally for every
    table this codebase ever constructs, well-formed or adversarial, this loop can never fail
    to terminate on a malformed dynamic-Huffman table. Malformed input is not silently accepted,
    though: a degenerate (incomplete) transmitted code tree still makes `decodeHuffmanSymbol`
    hit a `none` child, which surfaces as a clean `.error .corruptedHuffmanTree` -- see
    `Stdlib/Zlib/Test.lean`'s `corrupted dynamic Huffman table` case. -/
def decompress (bytes : ByteArray) : Except ZlibError ByteArray :=
  let rec go (curR : BitReader) (curOut : ByteArray) : Except ZlibError ByteArray :=
    match hbf : readBits curR 1 with
    | .error e => .error e
    | .ok (rBfinal, bfinal) =>
      match hbt : readBits rBfinal 2 with
      | .error e => .error e
      | .ok (rBtype, btype) =>
        match btype with
        | 0 =>
          match hblk : decodeStoredBlock rBtype curOut with
          | .error e => .error e
          | .ok (nextR, nextOut) =>
            if bfinal == 1 then .ok nextOut else go nextR nextOut
        | 1 =>
          match hstream : decodeHuffmanStream rBtype fixedLitLenTable fixedDistTable
              (buildHuffmanTable_isBranch fixedLitLenLengths 9)
              (buildHuffmanTable_isBranch fixedDistLengths 5) curOut with
          | .error e => .error e
          | .ok (nextR, nextOut) =>
            if bfinal == 1 then .ok nextOut else go nextR nextOut
        | 2 =>
          match htab : decodeDynamicTables rBtype with
          | .error e => .error e
          | .ok (rTables, litTbl, distTbl) =>
            match hstream : decodeHuffmanStream rTables litTbl distTbl
                (decodeDynamicTables_isBranch rBtype rTables litTbl distTbl htab).1
                (decodeDynamicTables_isBranch rBtype rTables litTbl distTbl htab).2 curOut with
            | .error e => .error e
            | .ok (nextR, nextOut) =>
              if bfinal == 1 then .ok nextOut else go nextR nextOut
        | _ => .error (.invalidBlockType btype)
  termination_by remainingBits curR
  decreasing_by
    · have h1 := readBits_remainingBits curR 1 rBfinal bfinal hbf
      have h2 := readBits_remainingBits rBfinal 2 rBtype _ hbt
      have h3 := decodeStoredBlock_remainingBits_le rBtype curOut nextR nextOut hblk
      omega
    · have h1 := readBits_remainingBits curR 1 rBfinal bfinal hbf
      have h2 := readBits_remainingBits rBfinal 2 rBtype _ hbt
      have h3 := decodeHuffmanStream_remainingBits_le rBtype fixedLitLenTable fixedDistTable
        (buildHuffmanTable_isBranch fixedLitLenLengths 9) (buildHuffmanTable_isBranch fixedDistLengths 5)
        curOut nextR nextOut hstream
      omega
    · have h1 := readBits_remainingBits curR 1 rBfinal bfinal hbf
      have h2 := readBits_remainingBits rBfinal 2 rBtype _ hbt
      have h3 := (decodeDynamicTables_bridge rBtype rTables litTbl distTbl htab).1
      have h4 := decodeHuffmanStream_remainingBits_le rTables litTbl distTbl
        (decodeDynamicTables_isBranch rBtype rTables litTbl distTbl htab).1
        (decodeDynamicTables_isBranch rBtype rTables litTbl distTbl htab).2
        curOut nextR nextOut hstream
      omega
  go (mkBitReader bytes) ByteArray.empty

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Reverses the lowest `len` bits of a number for LSB-first bitstream packing. -/
def reverseBits (code : Nat) (len : Nat) : Nat :=
  Id.run do
    let mut res := 0
    let mut c := code
    for _ in [0:len] do
      res := (res <<< 1) ||| (c &&& 1)
      c := c >>> 1
    res

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Encodes match length (3..258) into symbol code, extra bit count, and extra bit value. -/
def encodeLength (len : Nat) : (Nat × Nat × Nat) :=
  if len < 3 then (257, 0, 0)
  else if len <= 10 then (257 + len - 3, 0, 0)
  else if len <= 12 then (265, 1, len - 11)
  else if len <= 14 then (266, 1, len - 13)
  else if len <= 16 then (267, 1, len - 15)
  else if len <= 18 then (268, 1, len - 17)
  else if len <= 22 then (269, 2, len - 19)
  else if len <= 26 then (270, 2, len - 23)
  else if len <= 30 then (271, 2, len - 27)
  else if len <= 34 then (272, 2, len - 31)
  else if len <= 42 then (273, 3, len - 35)
  else if len <= 50 then (274, 3, len - 43)
  else if len <= 58 then (275, 3, len - 51)
  else if len <= 66 then (276, 3, len - 59)
  else if len <= 82 then (277, 4, len - 67)
  else if len <= 98 then (278, 4, len - 83)
  else if len <= 114 then (279, 4, len - 99)
  else if len <= 130 then (280, 4, len - 115)
  else if len <= 162 then (281, 5, len - 131)
  else if len <= 194 then (282, 5, len - 163)
  else if len <= 226 then (283, 5, len - 195)
  else if len <= 257 then (284, 5, len - 227)
  else (285, 0, 0)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Encodes match backward distance (1..32768) into distance symbol code, extra bit count, and extra bit value. -/
def encodeDistance (dist : Nat) : (Nat × Nat × Nat) :=
  if dist <= 4 then (dist - 1, 0, 0)
  else if dist <= 6 then (4, 1, dist - 5)
  else if dist <= 8 then (5, 1, dist - 7)
  else if dist <= 12 then (6, 2, dist - 9)
  else if dist <= 16 then (7, 2, dist - 13)
  else if dist <= 24 then (8, 3, dist - 17)
  else if dist <= 32 then (9, 3, dist - 25)
  else if dist <= 48 then (10, 4, dist - 33)
  else if dist <= 64 then (11, 4, dist - 49)
  else if dist <= 96 then (12, 5, dist - 65)
  else if dist <= 128 then (13, 5, dist - 97)
  else if dist <= 192 then (14, 6, dist - 129)
  else if dist <= 256 then (15, 6, dist - 193)
  else if dist <= 384 then (16, 7, dist - 257)
  else if dist <= 512 then (17, 7, dist - 385)
  else if dist <= 768 then (18, 8, dist - 513)
  else if dist <= 1024 then (19, 8, dist - 769)
  else if dist <= 1536 then (20, 9, dist - 1025)
  else if dist <= 2048 then (21, 9, dist - 1537)
  else if dist <= 3072 then (22, 10, dist - 2049)
  else if dist <= 4096 then (23, 10, dist - 3073)
  else if dist <= 6144 then (24, 11, dist - 4097)
  else if dist <= 8192 then (25, 11, dist - 6145)
  else if dist <= 12288 then (26, 12, dist - 8193)
  else if dist <= 16384 then (27, 12, dist - 12289)
  else if dist <= 24576 then (28, 13, dist - 16385)
  else (29, 13, dist - 24577)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Inner match-extension step of the LZ77 search: the longest common run starting at
    `candidate` and `pos`, capped at `maxMatchLen`, counting up from `len`. Structural
    recursion on `fuel` -- never `partial`/`while` -- so equation lemmas exist for proofs,
    the same rule `tokenizeAux` below already follows. Every step advances `len` by one and
    stops at `maxMatchLen`, so `fuel = maxMatchLen - len` always suffices. -/
def matchExtend (data : ByteArray) (pos candidate maxMatchLen : Nat) : Nat → Nat → Nat
  | 0, len => len
  | fuel + 1, len =>
    if len < maxMatchLen && data.get! (candidate + len) == data.get! (pos + len) then
      matchExtend data pos candidate maxMatchLen fuel (len + 1)
    else len

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Outer candidate scan of the LZ77 search: walks `candidate` backwards from `pos` while it
    stays above `startLookback`, keeping the longest run seen so far, and stopping early on a
    maximal 258-byte match. Structural recursion on `fuel`, which carries the original
    `tries < maxTries` budget: the loop body ran at most `maxTries` times, so `fuel =
    maxTries` reproduces it exactly. -/
def matchScan (data : ByteArray) (pos startLookback maxMatchLen : Nat) :
    Nat → Nat → Nat → Nat → (Nat × Nat)
  | 0, _candidate, bestLen, bestDist => (bestLen, bestDist)
  | fuel + 1, candidate, bestLen, bestDist =>
    if candidate > startLookback then
      let candidate := candidate - 1
      if data.get! candidate == data.get! pos &&
         data.get! (candidate + 1) == data.get! (pos + 1) &&
         data.get! (candidate + 2) == data.get! (pos + 2) then
        let len := matchExtend data pos candidate maxMatchLen (maxMatchLen - 3) 3
        if len > bestLen then
          if len == 258 then (len, pos - candidate)
          else matchScan data pos startLookback maxMatchLen fuel candidate len (pos - candidate)
        else matchScan data pos startLookback maxMatchLen fuel candidate bestLen bestDist
      else matchScan data pos startLookback maxMatchLen fuel candidate bestLen bestDist
    else (bestLen, bestDist)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- LZ77 match search finding longest matching substring in sliding lookback window.
    Bit-identical to the `while`-loop form this replaces; `matchScan`/`matchExtend` document
    how the two loop budgets map onto structural fuel. -/
def findLongestMatch (data : ByteArray) (pos : Nat) (maxLookback : Nat := 32768) (maxTries : Nat := 128) : (Nat × Nat) :=
  let total := data.size
  if pos + 3 > total then (0, 0)
  else
    let startLookback := if pos > maxLookback then pos - maxLookback else 0
    let maxMatchLen := Nat.min 258 (total - pos)
    let best := matchScan data pos startLookback maxMatchLen maxTries pos 0 0
    if best.1 >= 3 then best else (0, 0)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- An LZ77 token: either a literal byte or a (length, distance) back-reference. -/
inductive LZToken where
  | lit (b : UInt8)
  | ref (len dist : Nat)
  deriving Repr, DecidableEq, Inhabited

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Certifies a candidate LZ77 back-reference at `pos`: RFC 1951 length/distance ranges,
    in-bounds source window, and byte-for-byte agreement of the referenced span with the data
    it claims to repeat. `data.get! (pos - dist + i)` with `i` possibly `≥ dist` is exactly
    the decoder's self-overlapping copy semantics (RFC 1951 §3.2.3, "the referenced string
    may overlap the current position"). The match *search* (`findLongestMatch`) is an
    untrusted heuristic; this total checker is what the tokenizer actually relies on, so a
    future roundtrip proof needs only this predicate, never the search's internals. -/
def matchValid (data : ByteArray) (pos len dist : Nat) : Bool :=
  3 ≤ len && len ≤ 258 && 1 ≤ dist && dist ≤ 32768 && dist ≤ pos &&
  pos + len ≤ data.size &&
  (List.range len).all (fun i => data.get! (pos - dist + i) == data.get! (pos + i))

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Greedy LZ77 tokenizer worker: at each position take the longest *certified* match
    (falling back to a literal when the search returns nothing certifiable). Structural
    recursion on `fuel` — never `partial`/`while` — so equation lemmas exist for future
    proofs. Every step advances `pos` by at least 1, so `fuel = data.size` always suffices. -/
def tokenizeAux (data : ByteArray) : Nat → Nat → Array LZToken → Array LZToken
  | 0, _, acc => acc
  | fuel + 1, pos, acc =>
    if pos < data.size then
      let m := findLongestMatch data pos 32768 128
      if 3 ≤ m.1 ∧ matchValid data pos m.1 m.2 = true then
        tokenizeAux data fuel (pos + m.1) (acc.push (.ref m.1 m.2))
      else
        tokenizeAux data fuel (pos + 1) (acc.push (.lit (data.get! pos)))
    else acc

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Greedy LZ77 tokenization of an entire input buffer. -/
def tokenize (data : ByteArray) : Array LZToken :=
  tokenizeAux data data.size 0 #[]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Reference token-layer back-reference copy: append `len` bytes read `dist` positions back,
    one at a time — byte-for-byte the self-overlap semantics of `decodeHuffmanStream`'s
    RFC 1951 §3.2.3 match-copy loop, as a total structural recursion the kernel can induct
    on. -/
def lzCopy (dist : Nat) : Nat → ByteArray → ByteArray
  | 0, out => out
  | k + 1, out => lzCopy dist k (out.push (out.get! (out.size - dist)))

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Reference token-layer decode of a single LZ77 token onto an output accumulator. -/
def expandToken (out : ByteArray) : LZToken → ByteArray
  | .lit b => out.push b
  | .ref len dist => lzCopy dist len out

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Reference token-layer decode of an LZ77 token stream from an empty accumulator. This is
    the layer of `decompress` below Huffman coding and bitstream framing; `Stdlib/Zlib/
    Equivalence.lean`'s `lz77_roundtrip_soundness` proves `∀ data, expandTokens (tokenize
    data) = data` — the LZ77 half of the PA16 roundtrip decomposition. -/
def expandTokens (tokens : Array LZToken) : ByteArray :=
  tokens.foldl expandToken ByteArray.empty


/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits one Huffman-coded symbol (canonical code bit-reversed for LSB-first packing).
    A symbol absent from the table is a plan-construction bug; it emits nothing, which the
    differential fuzzers detect as a corrupt stream rather than masking silently. -/
def emitHuffSymbol (w : BitWriter) (table : HuffmanTable) (sym : Nat) : BitWriter :=
  match table.codes[sym]! with
  | some (code, len) => writeBits w (reverseBits code len) len
  | none => w

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits one LZ77 token under the given literal/length and distance Huffman tables. -/
def emitToken (litTable distTable : HuffmanTable) (w : BitWriter) (t : LZToken) : BitWriter :=
  match t with
  | .lit b => emitHuffSymbol w litTable b.toNat
  | .ref len dist =>
    let (lenCode, lenEB, lenEV) := encodeLength len
    let w := emitHuffSymbol w litTable lenCode
    let w := if lenEB > 0 then writeBits w lenEV lenEB else w
    let (distCode, distEB, distEV) := encodeDistance dist
    let w := emitHuffSymbol w distTable distCode
    if distEB > 0 then writeBits w distEV distEB else w

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits a complete token stream followed by the end-of-block symbol 256. -/
def emitTokens (litTable distTable : HuffmanTable) (w : BitWriter) (tokens : Array LZToken) : BitWriter :=
  let w := tokens.foldl (emitToken litTable distTable) w
  emitHuffSymbol w litTable 256

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits a final (BFINAL=1) fixed-Huffman block (BTYPE=01) for a token stream. -/
def emitFixedBlock (tokens : Array LZToken) : BitWriter :=
  let w : BitWriter := {}
  let w := writeBits w 1 1
  let w := writeBits w 1 2
  emitTokens fixedLitLenTable fixedDistTable w tokens

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Body of `compressFixed`'s emit loop: from `pos`, emit one LZ77 token's fixed-Huffman
    codes into `w` and continue. Structural recursion on `fuel` -- never `partial`/`while` --
    so equation lemmas exist for proofs, the same rule `tokenizeAux` follows. Every step
    advances `pos` by at least 1 (a certified match advances by `matchLen >= 3`, a literal by
    1), so `fuel = data.size` always suffices. -/
def compressFixedLoop (data : ByteArray) : Nat → BitWriter → Nat → BitWriter
  | 0, w, _pos => w
  | fuel + 1, w, pos =>
    if pos < data.size then
      let (matchLen, matchDist) := findLongestMatch data pos 32768 128
      if matchLen >= 3 then
        -- 1. Emit Length Code + extra bits
        let (lenSymbol, lenExtraBits, lenExtraVal) :=
          if matchLen == 258 then (285, 0, 0)
          else if matchLen <= 10 then (257 + matchLen - 3, 0, 0)
          else if matchLen <= 18 then (265 + (matchLen - 11) / 2, 1, (matchLen - 11) &&& 1)
          else if matchLen <= 34 then (269 + (matchLen - 19) / 4, 2, (matchLen - 19) &&& 3)
          else if matchLen <= 66 then (273 + (matchLen - 35) / 8, 3, (matchLen - 35) &&& 7)
          else if matchLen <= 130 then (277 + (matchLen - 67) / 16, 4, (matchLen - 67) &&& 15)
          else (281 + (matchLen - 131) / 32, 5, (matchLen - 131) &&& 31)
        let w :=
          if lenSymbol <= 279 then writeBits w (reverseBits (lenSymbol - 256) 7) 7
          else writeBits w (reverseBits (lenSymbol - 280 + 0xC0) 8) 8
        let w := if lenExtraBits > 0 then writeBits w lenExtraVal lenExtraBits else w
        -- 2. Emit Distance Code + extra bits (5-bit Fixed Huffman distance code = rev5(distCode))
        let (distCode, distExtraBits, distExtraVal) := encodeDistance matchDist
        let w := writeBits w (reverseBits distCode 5) 5
        let w := if distExtraBits > 0 then writeBits w distExtraVal distExtraBits else w
        compressFixedLoop data fuel w (pos + matchLen)
      else
        let byteVal := (data.get! pos).toNat
        let w :=
          if byteVal <= 143 then writeBits w (reverseBits (byteVal + 0x30) 8) 8
          else writeBits w (reverseBits (byteVal - 144 + 0x190) 9) 9
        compressFixedLoop data fuel w (pos + 1)
    else w

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Pure RFC 1951 Fixed Huffman block compressor matching assembly machine code engine.
    Bit-identical to the `while`-loop form this replaces; `compressFixedLoop` carries the
    loop body as structural fuel recursion. -/
def compressFixed (data : ByteArray) : ByteArray :=
  -- BFINAL = 1 (1 bit), BTYPE = 01 (2 bits) -> 3 bits of 0b011 = 3
  let w : BitWriter := writeBits {} 3 3
  let w := compressFixedLoop data data.size w 0
  -- End of block (symbol 256 = 7 bits of 0)
  flushBitWriter (writeBits w 0 7)

end Grass.Std.Zlib.Deflate
