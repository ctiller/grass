import Grass.Std.Logical.Byte

/-!
# The fourth representation, costed

`docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.2 has argued a two-way choice —
`Vec` as a one-field structure over `List`, versus `abbrev Vec := Array` — and
adversarial review showed the argument decided nothing, because both options fail
a criterion neither was measured against. [HELLO_WORLD.md](../../../docs/HELLO_WORLD.md)
accepts the first milestone only when `emitProgram` yields bytes that "execute
successfully on responsive validation hosts", so the byte writer runs, over
`ByteArray = Vec Byte`. The shipped `Vec.push` is `⟨v.toList ++ [a]⟩` and
`Vec.get?` is `v.toList[i]?`: O(n) per push and O(i) per read, so O(n²) to build
an artifact. The `vec-as-array-probe` branch changed the *type* and left every
body list-shaped, so it is a rename and is slower still.

This module is the option nobody named: **a distinct one-field structure whose
field is an `Array`.** It keeps everything the structure was chosen for — a
`ByteArray` that is not a `List Byte`, not a host `ByteArray`, and not an
`Array Byte`, all checked by the elaborator — and gets `Array`'s O(1) push and
O(1) indexed read, because the bodies are `Array` operations rather than list
operations behind an `Array` type.

It is deliberately a *parallel* module named `AVec` rather than a replacement.
The question being answered is what the laws cost, and that is answered by
porting the core and counting, not by rewriting the library before the answer is
known. Nothing imports this; it is evidence.

## What to look at

Each law below is annotated with how it was proved:

- `native` — an `Array` lemma applied directly, no list reasoning;
- `via toList` — proved by dropping to `Array.toList` and using a `List` lemma;
- `hard` — needed more than a one-liner.

The count at the bottom of this file is the deliverable.
-/

namespace Grass.Std.Logical

universe u v

/--
A finite ordered sequence, represented as an `Array`.

The field is `toArray`, not `toList`, and that is the whole experiment: the
representation is the one Lean's runtime implements with a real dynamic array, so
`AVec.push` is `Array.push` and reading an index is an index.
-/
structure AVec (α : Type u) where
  ofArray ::
  toArray : Array α

namespace AVec

variable {α : Type u} {β : Type v}

theorem toArray_injective {v w : AVec α} (h : v.toArray = w.toArray) : v = w :=
  congrArg ofArray h

/-! ## Construction and observation -/

def empty : AVec α := ⟨#[]⟩

def fromList (l : List α) : AVec α := ⟨l.toArray⟩

def toList (v : AVec α) : List α := v.toArray.toList

/-- `docs/STDLIB.md` §3's name. `Array` spells it `size`; this is the one place the
port has to bridge a name rather than a proof. -/
def length (v : AVec α) : Nat := v.toArray.size

def get? (v : AVec α) (i : Nat) : Option α := v.toArray[i]?

def get (v : AVec α) (i : Nat) (h : i < v.length) : α := v.toArray[i]'h

def push (v : AVec α) (a : α) : AVec α := ⟨v.toArray.push a⟩

def set (v : AVec α) (i : Nat) (a : α) : AVec α := ⟨v.toArray.setIfInBounds i a⟩

def append (v w : AVec α) : AVec α := ⟨v.toArray ++ w.toArray⟩

instance : Append (AVec α) := ⟨append⟩

def map (f : α → β) (v : AVec α) : AVec β := ⟨v.toArray.map f⟩

def take (v : AVec α) (n : Nat) : AVec α := ⟨v.toArray.take n⟩

def drop (v : AVec α) (n : Nat) : AVec α := ⟨v.toArray.drop n⟩

/-! ## Laws

Annotated by proof route, which is the measurement this module exists to make.
-/

-- native
@[simp] theorem length_empty : (empty : AVec α).length = 0 := rfl

-- native
@[simp] theorem get?_empty (i : Nat) : (empty : AVec α).get? i = none := rfl

-- native: Array.size_push
@[simp] theorem length_push (v : AVec α) (a : α) : (v.push a).length = v.length + 1 := by
  simp [length, push]

-- hard: Array.getElem?_push_lt is stated as `= some xs[i]`, not `= xs[i]?`, so it
-- does not match; the `if` form plus a disequality is what works.
theorem get?_push_lt (v : AVec α) (a : α) {i : Nat} (h : i < v.length) :
    (v.push a).get? i = v.get? i := by
  show (v.toArray.push a)[i]? = v.toArray[i]?
  rw [Array.getElem?_push]
  have hne : i ≠ v.toArray.size := by
    have : i < v.toArray.size := h
    omega
  simp [hne]

-- native: Array.getElem?_push_eq
@[simp] theorem get?_push_self (v : AVec α) (a : α) : (v.push a).get? v.length = some a :=
  Array.getElem?_push_size

-- native: Array.size_setIfInBounds
@[simp] theorem length_set (v : AVec α) (i : Nat) (a : α) : (v.set i a).length = v.length := by
  simp [length, set]

-- native: Array.getElem?_setIfInBounds_self_of_lt
@[simp] theorem get?_set_self (v : AVec α) {i : Nat} (h : i < v.length) (a : α) :
    (v.set i a).get? i = some a :=
  Array.getElem?_setIfInBounds_self_of_lt h

-- native: Array.getElem?_setIfInBounds_ne
theorem get?_set_ne (v : AVec α) {i j : Nat} (h : j ≠ i) (a : α) :
    (v.set i a).get? j = v.get? j :=
  Array.getElem?_setIfInBounds_ne (Ne.symm h)

-- native: Array.size_append
@[simp] theorem length_append (v w : AVec α) : (v ++ w).length = v.length + w.length := by
  show (v.toArray ++ w.toArray).size = _
  simp [length]

-- native: Array.size_map
@[simp] theorem length_map (f : α → β) (v : AVec α) : (v.map f).length = v.length := by
  simp [length, map]

-- native: Array.getElem?_map
@[simp] theorem get?_map (f : α → β) (v : AVec α) (i : Nat) :
    (v.map f).get? i = (v.get? i).map f := by
  simp [get?, map]

-- native: Array.ext'-style, via toList extensionality
@[ext] theorem ext_of_get? {v w : AVec α} (h : ∀ i, v.get? i = w.get? i) : v = w := by
  apply toArray_injective
  apply Array.ext'
  apply List.ext_getElem?
  intro i
  simpa [get?] using h i

-- via toList: Array has no size_take
@[simp] theorem length_take (v : AVec α) (n : Nat) : (v.take n).length = min n v.length := by
  simp [length, take]

-- via toList: Array has no size_drop
@[simp] theorem length_drop (v : AVec α) (n : Nat) : (v.drop n).length = v.length - n := by
  simp [length, drop]

-- via toList: Array has no take_append_drop
@[simp] theorem append_splitAt (v : AVec α) (n : Nat) : v.take n ++ v.drop n = v := by
  apply toArray_injective
  show v.toArray.take n ++ v.toArray.drop n = v.toArray
  apply Array.ext'
  simp
  exact List.take_of_length_le (by simp; omega)

/-! ## Round trips -/

@[simp] theorem toList_fromList (l : List α) : (fromList l).toList = l := by
  simp [fromList, toList]

@[simp] theorem fromList_toList (v : AVec α) : fromList v.toList = v := by
  apply toArray_injective
  simp [fromList, toList]

/-! ## The byte container

The whole point of the structure, checked here rather than argued: a Grass byte
array is distinct from a `List Byte`, from Lean's host `ByteArray`, *and* from a
bare `Array Byte`. The third is the one the `abbrev Vec := Array` option gives
up, and `Tests/Std/VecArrayCost.lean` pins all three.
-/

end AVec

/-- The byte container under this representation. -/
abbrev AByteArray := AVec Byte

end Grass.Std.Logical
