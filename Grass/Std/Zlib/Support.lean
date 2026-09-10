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

/-
## Generic `ByteArray` push/get! plumbing (PA10, hoisted for PA16)

Accumulator-growing `Id.run`/`for`/`push` loops that read back their own `.get!`-indexed
output need to know how `.get!` interacts with `.push` on an otherwise-arbitrary
`ByteArray`. Lean core proves the analogous facts for the derived `GetElem!` notation
(`[i]!`, `ByteArray.getElem!_push_lt`/`_eq` in `Init/Data/ByteArray/Lemmas.lean`) but not
for `.get!` itself (a separate, directly `@[extern]`-implemented function, not defined in
terms of `[i]!`). These lemmas bridge that gap once. Originally proven for PA10 in
`Stdlib/Png/Equivalence.lean` (whose own header noted they are not PNG-specific and should
be reused rather than re-derived); hoisted here unchanged so `Stdlib/Zlib`'s LZ77/DEFLATE
equivalence proofs can import them without a Zlib → Png dependency inversion.
-/

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- `.get!` agrees with the `[i]!` notation Lean core's own `ByteArray` lemmas are stated
    over, for any in-bounds index. -/
theorem ByteArray.get!_eq_getElem_bang (data : ByteArray) (i : Nat) (h : i < data.size) :
    data.get! i = data[i]! := by
  rw [getElem!_pos data i h]
  simp only [ByteArray.get!]
  rw [getElem!_pos data.data i h]
  rfl

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- `.get!` agrees with the proof-carrying `getElem`, for any in-bounds index -- the form
    `ByteArray.ext_getElem` needs. -/
theorem ByteArray.get!_eq_getElem (data : ByteArray) (i : Nat) (h : i < data.size) :
    data.get! i = data[i]'h := by
  rw [ByteArray.get!_eq_getElem_bang data i h, getElem!_pos data i h]

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Pushing a new byte never disturbs any earlier index -- the fact that lets an induction
    along output position carry its "already-reconstructed prefix" invariant across a
    `push`. -/
theorem ByteArray.get!_push_lt (data : ByteArray) (b : UInt8) (i : Nat) (hi : i < data.size) :
    (data.push b).get! i = data.get! i := by
  have hi' : i < (data.push b).size := by rw [ByteArray.size_push]; omega
  rw [ByteArray.get!_eq_getElem_bang (data.push b) i hi', ByteArray.get!_eq_getElem_bang data i hi,
    ByteArray.getElem!_push_lt data b i hi]

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- The byte a `push` appends is exactly what `.get!` reads back at the (pre-push) size --
    the induction's base case for the newly-written position. Phrased with an explicit
    `i = data.size` hypothesis (rather than only `data.size` itself) so it rewrites directly
    against a goal whose index is some other named variable already proven equal to the
    size. -/
theorem ByteArray.get!_push_eq (data : ByteArray) (b : UInt8) (i : Nat) (hi : i = data.size) :
    (data.push b).get! i = b := by
  subst hi
  have h : data.size < (data.push b).size := by rw [ByteArray.size_push]; omega
  rw [ByteArray.get!_eq_getElem_bang (data.push b) data.size h, ByteArray.getElem!_push_eq data b]

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Two same-size `ByteArray`s that agree at every `.get!`-indexed position are equal --
    the closing step that lifts a pointwise induction to whole-`ByteArray` equality. -/
theorem ByteArray.ext_get! {a b : ByteArray} (hsize : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← ByteArray.get!_eq_getElem a i hi, ← ByteArray.get!_eq_getElem b i hi']
  exact h i hi
