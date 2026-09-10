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

namespace Grass.Std.Zlib.Deflate

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A canonical Huffman decode tree node. -/
inductive HuffmanNode where
  | leaf (symbol : Nat)
  | branch (left : Option HuffmanNode) (right : Option HuffmanNode)
  deriving Repr, Inhabited

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Structure containing both encoding table and decoding tree for a Huffman alphabet. -/
structure HuffmanTable where
  maxBits : Nat
  codes   : Array (Option (Nat × Nat)) -- symbol -> Option (code, bitLength)
  root    : HuffmanNode
  deriving Repr, Inhabited

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Inserts a canonical prefix code into a binary decode tree. -/
def insertCode (root : HuffmanNode) (symbol : Nat) (code : Nat) (len : Nat) : HuffmanNode :=
  let rec loop (node : HuffmanNode) (curCode : Nat) (remainingBits : Nat) : HuffmanNode :=
    match remainingBits with
    | 0 => HuffmanNode.leaf symbol
    | bits + 1 =>
      let bit := (curCode >>> bits) &&& 1
      match node with
      | HuffmanNode.leaf _ =>
        -- Overwrite branch if needed
        if bit == 0 then
          HuffmanNode.branch (some (loop (HuffmanNode.branch none none) curCode bits)) none
        else
          HuffmanNode.branch none (some (loop (HuffmanNode.branch none none) curCode bits))
      | HuffmanNode.branch l r =>
        if bit == 0 then
          let nextL := match l with | some n => n | none => HuffmanNode.branch none none
          HuffmanNode.branch (some (loop nextL curCode bits)) r
        else
          let nextR := match r with | some n => n | none => HuffmanNode.branch none none
          HuffmanNode.branch l (some (loop nextR curCode bits))
  loop root code len

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- For any starting decode tree `root` and any positive code length `bits + 1`,
    `insertCode` returns a `branch`-rooted tree -- regardless of `root`'s own prior shape.
    `insertCode`'s recursion only ever descends into and replaces a *child* of the root
    (`insertCode.loop`'s `remainingBits = 0` case, which alone can yield a bare `leaf`, only
    fires after `bits` further steps); the root position itself is rewritten by exactly one of
    `insertCode.loop`'s `branch`-armed equations, all of which produce `HuffmanNode.branch`
    outright. This is the load-bearing fact behind `buildHuffmanTable_isBranch`: it holds for
    *every* length array, well-formed or adversarial, since it never inspects `root`. -/
theorem insertCode_isBranch (root : HuffmanNode) (symbol code bits : Nat) :
    ∃ l r, insertCode root symbol code (bits + 1) = HuffmanNode.branch l r := by
  unfold insertCode
  cases root with
  | leaf s => rw [insertCode.loop.eq_def]; dsimp only; split <;> exact ⟨_, _, rfl⟩
  | branch l r => rw [insertCode.loop.eq_def]; dsimp only; split <;> exact ⟨_, _, rfl⟩

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `buildHuffmanTable`'s third pass (RFC 1951 §3.2.2 code assignment + decode-tree insertion),
    expressed as structural recursion on `fuel` (remaining symbols to process) rather than a
    `for` loop over `[0:numSymbols]`, so its effect on `root` is provable by induction on `fuel`
    -- see `buildHuffmanTreeAssign_isBranch`. Called with `fuel := numSymbols`, `pos := 0`, this
    is exactly `buildHuffmanTable`'s original loop: for symbol `pos`, if its length is in range
    `(0, maxBits]`, assign it the next canonical code of that length, record it in `codes`, and
    insert it into the decode tree; otherwise leave `nextCode`/`codes`/`root` untouched; then
    advance to `pos + 1`. -/
def buildHuffmanTreeAssign (lengths : Array Nat) (maxBits : Nat) :
    Nat → Nat → Array Nat → Array (Option (Nat × Nat)) → HuffmanNode →
    Array (Option (Nat × Nat)) × Array Nat × HuffmanNode
  | 0, _pos, nextCode, codes, root => (codes, nextCode, root)
  | fuel + 1, pos, nextCode, codes, root =>
    let len := lengths[pos]!
    if len > 0 && len <= maxBits then
      let symCode := nextCode[len]!
      let nextCode' := nextCode.set! len (symCode + 1)
      let codes' := codes.set! pos (some (symCode, len))
      let root' := insertCode root pos symCode len
      buildHuffmanTreeAssign lengths maxBits fuel (pos + 1) nextCode' codes' root'
    else
      buildHuffmanTreeAssign lengths maxBits fuel (pos + 1) nextCode codes root

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `buildHuffmanTreeAssign` never turns a branch-rooted tree into a leaf: every update it
    makes to `root` factors through `insertCode _ _ _ len` with `len > 0` (guarded by the same
    `len > 0 && len <= maxBits` test the update is gated on), which `insertCode_isBranch` shows
    always yields a `branch`, regardless of the tree it started from -- so induction on `fuel`
    needs no fact about `lengths` at all, well-formed or adversarial. -/
theorem buildHuffmanTreeAssign_isBranch (lengths : Array Nat) (maxBits : Nat) :
    ∀ (fuel pos : Nat) (nextCode : Array Nat) (codes : Array (Option (Nat × Nat)))
      (root : HuffmanNode),
      (∃ l r, root = HuffmanNode.branch l r) →
      ∃ l r, (buildHuffmanTreeAssign lengths maxBits fuel pos nextCode codes root).2.2
        = HuffmanNode.branch l r := by
  intro fuel
  induction fuel with
  | zero => intro pos nextCode codes root hroot; simpa [buildHuffmanTreeAssign] using hroot
  | succ fuel ih =>
    intro pos nextCode codes root hroot
    simp only [buildHuffmanTreeAssign]
    split
    · obtain ⟨bits, hbits⟩ : ∃ bits, lengths[pos]! = bits + 1 := by
        rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact ⟨lengths[pos]! - 1, by omega⟩
      rw [hbits]
      exact ih _ _ _ _ (insertCode_isBranch root pos nextCode[bits + 1]! bits)
    · exact ih _ _ _ _ hroot

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Builds a canonical Huffman table from an array of symbol bit lengths (RFC 1951 §3.2.2).
    The code-length-counting (`blCount`) and starting-code (`nextCode`) passes are unchanged
    imperative `for` loops; the third pass (assigning codes to symbols and inserting them into
    the decode tree) is `buildHuffmanTreeAssign`, structural recursion on the remaining symbol
    count rather than a `for`/`while` loop, so its "root stays branch-rooted" effect is provable
    by plain induction -- see `buildHuffmanTreeAssign_isBranch` / `buildHuffmanTable_isBranch`. -/
def buildHuffmanTable (lengths : Array Nat) (maxBits : Nat := 15) : HuffmanTable :=
  Id.run do
    let numSymbols := lengths.size
    -- Step 1: Count codes of each length
    let mut blCount : Array Nat := Array.replicate (maxBits + 1) 0
    for i in [0:numSymbols] do
      let len := lengths[i]!
      if len > 0 && len <= maxBits then
        blCount := blCount.set! len (blCount[len]! + 1)

    -- Step 2: Find starting code for each length
    let mut code := 0
    let mut nextCode : Array Nat := Array.replicate (maxBits + 1) 0
    for bits in [1:maxBits + 1] do
      code := (code + blCount[bits - 1]!) <<< 1
      nextCode := nextCode.set! bits code

    -- Step 3: Assign numerical codes to symbols & construct decode tree
    let (codes, _nextCodeFinal, root) :=
      buildHuffmanTreeAssign lengths maxBits numSymbols 0 nextCode
        (Array.replicate numSymbols none) (HuffmanNode.branch none none)

    { maxBits := maxBits, codes := codes, root := root }

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `buildHuffmanTable`'s output `root` is exactly `buildHuffmanTreeAssign`'s third-pass
    result, for whatever `nextCode` array steps 1-2 (code-length counting, starting-code
    computation -- untouched by this refactor, and irrelevant to `root`) happen to produce.
    Purely a bridging lemma so `buildHuffmanTable_isBranch` doesn't need to reduce through the
    `for`-loop machinery of steps 1-2 itself; `rfl` here evaluates the whole `Id.run do` block,
    letting unification pick out the actual `nextCode` value rather than needing it spelled out. -/
theorem buildHuffmanTable_root_eq (lengths : Array Nat) (maxBits : Nat) :
    ∃ nc, (buildHuffmanTable lengths maxBits).root =
      (buildHuffmanTreeAssign lengths maxBits lengths.size 0 nc
        (Array.replicate lengths.size none) (HuffmanNode.branch none none)).2.2 := by
  unfold buildHuffmanTable
  exact ⟨_, rfl⟩

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- **The type-level gap this file closes**: `buildHuffmanTable` -- the *only* way this
    codebase ever constructs a `HuffmanTable` (fixed tables via `buildHuffmanTable
    fixedLitLenLengths`/`fixedDistLengths`, dynamic tables via `buildHuffmanTable` on decoded,
    untrusted code lengths in `decodeDynamicTables`) -- always produces a `branch`-rooted decode
    tree, *unconditionally*: for every `lengths` array, well-formed canonical-Huffman input or
    adversarial garbage alike, and regardless of `maxBits`. There is no malformed transmitted
    code-length sequence that makes `buildHuffmanTable` return a `leaf`-rooted (and hence,
    per `decodeHuffmanSymbol_remainingBits_lt` in `Deflate.lean`, zero-bit-consuming) table --
    the non-termination scenario motivating this invariant is real for a *hand-constructed*
    `HuffmanTable` literal, but unreachable through this codebase's sole constructor. -/
theorem buildHuffmanTable_isBranch (lengths : Array Nat) (maxBits : Nat) :
    ∃ l r, (buildHuffmanTable lengths maxBits).root = HuffmanNode.branch l r := by
  obtain ⟨nc, hnc⟩ := buildHuffmanTable_root_eq lengths maxBits
  rw [hnc]
  exact buildHuffmanTreeAssign_isBranch lengths maxBits lengths.size 0 nc _ _ ⟨none, none, rfl⟩

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Generates the RFC 1951 §3.2.6 Fixed Literal/Length bit length array (288 symbols). -/
def fixedLitLenLengths : Array Nat :=
  Id.run do
    let mut arr : Array Nat := Array.replicate 288 0
    for i in [0:144] do
      arr := arr.set! i 8
    for i in [144:256] do
      arr := arr.set! i 9
    for i in [256:280] do
      arr := arr.set! i 7
    for i in [280:288] do
      arr := arr.set! i 8
    arr

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Generates the RFC 1951 §3.2.6 Fixed Distance bit length array (32 symbols, each 5 bits). -/
def fixedDistLengths : Array Nat :=
  Array.replicate 32 5

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Prebuilt RFC 1951 Fixed Literal/Length Huffman Table. -/
def fixedLitLenTable : HuffmanTable :=
  buildHuffmanTable fixedLitLenLengths 9

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Prebuilt RFC 1951 Fixed Distance Huffman Table. -/
def fixedDistTable : HuffmanTable :=
  buildHuffmanTable fixedDistLengths 5

end Grass.Std.Zlib.Deflate
