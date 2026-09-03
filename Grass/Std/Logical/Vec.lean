import Grass.Std.Logical.Byte

/-!
# Finite ordered sequences

`docs/STDLIB.md` §1 names `Vec α` the fundamental finite ordered dynamic array
and fixes the consequence that matters most for the rest of the repository:

> Grass must not introduce a second unrelated byte-container primitive.

`ByteArray := Vec Byte` is the early public name that rule protects, so `Vec`
has to exist before the memory, artifact, decoder, and program layers reach for
a byte container of their own. `Grass/Std/Logical/Byte.lean` records exactly
that: `Byte` is defined there and `Vec` deliberately is not, because the design
belongs to this module's owner.

## What this type is, and what it is not

`Vec α` here is the *logical* sequence of `docs/STDLIB.md` §1:

> `Vec α` itself is a pure finite sequence. Its equality and high-level laws are
> extensional over length and indexed elements, independent of capacity,
> allocator choice, or address.

There is no capacity, no allocator, no buffer identity, and no loan. Those
belong to `OwnedVec profile α vecId bufferId` in `Grass.Std.Owned`, which
`docs/MODULES.md` places *above* the memory and obligation layers precisely so
that this module can sit below them. `Represents` is the connection, and it is
`Std.Owned`'s to state; nothing here anticipates it.

## Why a structure over `List` rather than an abbreviation

`Vec α` wraps `List α` in a one-field structure. An `abbrev` would be shorter
and is the wrong choice for three reasons.

The first is the §1 rule quoted above. If `Vec α` reduced to `List α`, then
`ByteArray` would reduce to `List Byte`, and Lean's `List` API — not the
reviewed surface in `docs/STDLIB.md` §3 — would become the de facto byte-array
interface for every consumer. A distinct type makes "this is a `ByteArray`" a
statement the elaborator checks rather than a naming convention.

The second is that `docs/STDLIB.md` §4 separates capacity growth policy from
logical equality, and makes complexity a matter of separately named profile
theorems rather than of functional correctness. A one-field structure keeps a seam at which the representation can be
replaced without touching a consumer, since consumers write `Vec.get?` and not
`List.get?`.

The third is `docs/MODULES.md`'s prohibition on competing foundations. The
narrower the door into the representation, the fewer places a lower layer can
grow its own ordered buffer by accident.

The cost is real and is paid deliberately: every law here is a wrapper over a
`List` law, and `toList`/`fromList` are the only route between the two.

## Equality is propositional here, unlike `FiniteMap`

`Grass/Std/Logical/FiniteMap.lean` makes extensional agreement a separate
`Equiv` relation because its association lists are not normalized: two lists can
denote the same map. A reader arriving from that module should not expect the
same shape here, and the difference is not a matter of taste.

A `Vec` has exactly one representation per length-and-elements, so extensionality
is provable *as an equality*: `Vec.ext_of_get?` concludes `v = w`, not
`v.Equiv w`. There is therefore no `Vec.Equiv`, and `=` is the relation every
law and every consumer should use.

## What is deliberately absent

`docs/STDLIB.md` §3 lists a wider pure interface than this module implements,
and §6 says only structures demanded by a milestone are implemented. Absent, and
why:

- `mapM` and `traverse` need an effect vocabulary. `docs/STDLIB.md` §5 asks for
  *order preservation* for traverse, which is a statement about the order of
  effects and not just of results, so it needs the law-bearing monad interface
  `docs/MODULES.md` assigns to `Grass.Effect`. Writing them over Lean's bare
  `Monad` now would fix the wrong contract.
- `foldMap` needs a monoid vocabulary that no consumer has demanded.
- Lexicographic comparison needs an ordering vocabulary, likewise undemanded.
- `insertAt` and `eraseAt` are present with their length laws, but their indexing
  laws are not: no consumer indexes into a `Vec` across an insertion yet, and
  those laws are large enough to be worth writing against a real use.

Each is an open item in `docs/STDLIB_IMPLEMENTATION_PLAN.md` rather than a
silent gap.
-/

namespace Grass.Std.Logical

universe u v w

/--
A finite ordered sequence of `α` values.

The logical container of `docs/STDLIB.md` §1: length and indexed elements are
all there is to one. Capacity, allocation, and ownership belong to `OwnedVec`, in
`Grass.Std.Owned`.

`fromList` is the constructor and `toList` the field, so the two round-trip
definitionally; see `Vec.toList_fromList` and `Vec.fromList_toList`.
-/
abbrev Vec := Array

namespace Vec

/-- Build a `Vec` from a list in the same order. -/
def fromList {α : Type u} (l : List α) : Vec α := ⟨l⟩

end Vec

namespace Vec

variable {α : Type u} {β : Type v} {γ : Type w}

@[simp] theorem toList_fromList (l : List α) : (fromList l).toList = l := rfl

@[simp] theorem fromList_toList (v : Vec α) : fromList v.toList = v := rfl

theorem toList_injective {v w : Vec α} (h : v.toList = w.toList) : v = w :=
  congrArg fromList h

/-!
## Construction
-/

/-- The sequence with no elements. -/
def empty : Vec α := ⟨[]⟩

instance : EmptyCollection (Vec α) := ⟨empty⟩

instance : Inhabited (Vec α) := ⟨empty⟩

/-- The one-element sequence. -/
def singleton (a : α) : Vec α := ⟨[a]⟩

/-- `n` copies of `a`, in order. -/
def replicate (n : Nat) (a : α) : Vec α := ⟨List.replicate n a⟩

/-!
## Observation
-/

/-- The number of elements. -/
def length (v : Vec α) : Nat := v.toList.length

/-- Whether the sequence has no elements. See `Vec.isEmpty_iff_length_eq_zero`. -/
def isEmpty (v : Vec α) : Bool := v.toList.isEmpty

/-- The element at `i`, or `none` when `i` is out of range: the checked accessor of
`docs/STDLIB.md` §3. -/
def get? (v : Vec α) (i : Nat) : Option α := v.toList[i]?

/--
The element at `i`, given a proof that `i` is in range: the bounded accessor of
`docs/STDLIB.md` §3.

The proof argument is the mechanism. There is no default element and no
`Inhabited α`, so an out-of-range bounded read is not expressible rather than
being silently defaulted; `Vec.get?` is the accessor for a caller that does not
have the bound.
-/
def get (v : Vec α) (i : Nat) (h : i < v.length) : α := v.toList[i]'h

@[simp] theorem length_fromList (l : List α) : (fromList l).length = l.length := rfl

@[simp] theorem get?_fromList (l : List α) (i : Nat) : (fromList l).get? i = l[i]? := rfl

@[simp] theorem length_empty : (empty : Vec α).length = 0 := rfl

@[simp] theorem get?_empty (i : Nat) : (empty : Vec α).get? i = none := rfl

@[simp] theorem length_singleton (a : α) : (singleton a).length = 1 := rfl

@[simp] theorem get?_singleton_zero (a : α) : (singleton a).get? 0 = some a := rfl

@[simp] theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  simp [length, replicate]

theorem get?_replicate (n : Nat) (a : α) (i : Nat) :
    (replicate n a).get? i = if i < n then some a else none := by
  simp [get?, replicate, List.getElem?_replicate]

theorem isEmpty_iff_length_eq_zero (v : Vec α) : v.isEmpty = true ↔ v.length = 0 := by
  simp [isEmpty, length]

/-- The checked and bounded accessors agree wherever both apply. -/
theorem get?_eq_some_get (v : Vec α) (i : Nat) (h : i < v.length) :
    v.get? i = some (v.get i h) :=
  List.getElem?_eq_getElem h

theorem get?_eq_none (v : Vec α) {i : Nat} (h : v.length ≤ i) : v.get? i = none := by
  simp only [get?, List.getElem?_eq_none_iff]
  exact h

/-!
## Extensionality

`docs/STDLIB.md` §5 asks for "extensionality by length and indexed values". Both
shapes conclude propositional equality, for the reason in the module comment.
-/

/-- Two sequences agreeing at every index are equal. -/
@[ext] theorem ext_of_get? {v w : Vec α} (h : ∀ i, v.get? i = w.get? i) : v = w :=
  toList_injective (List.ext_getElem? h)

/-- The length-and-index shape of `Vec.ext_of_get?`. -/
theorem ext_of_get {v w : Vec α} (hlen : v.length = w.length)
    (h : ∀ i, (hv : i < v.length) → (hw : i < w.length) → v.get i hv = w.get i hw) :
    v = w :=
  toList_injective (List.ext_getElem hlen (fun i hv hw => h i hv hw))

/-!
## Update
-/

/-- Replace the element at `i`, or return the sequence unchanged when `i` is out of
range. `Vec.length_set` records that the length never moves. -/
def set (v : Vec α) (i : Nat) (a : α) : Vec α := ⟨v.toList.set i a⟩

@[simp] theorem length_set (v : Vec α) (i : Nat) (a : α) : (v.set i a).length = v.length := by
  simp [length, set]

@[simp] theorem get?_set_self (v : Vec α) {i : Nat} (h : i < v.length) (a : α) :
    (v.set i a).get? i = some a := by
  simp only [get?, set]
  rw [List.getElem?_set_self]
  exact h

theorem get?_set_ne (v : Vec α) {i j : Nat} (h : j ≠ i) (a : α) :
    (v.set i a).get? j = v.get? j := by
  simp only [get?, set]
  exact List.getElem?_set_ne (Ne.symm h)

/-- The combined framing law, in the shape a consumer applies it: an update is
visible at its own index and nowhere else. -/
theorem get?_set (v : Vec α) (i j : Nat) (a : α) :
    (v.set i a).get? j =
      if j = i then (if i < v.length then some a else none) else v.get? j := by
  by_cases h : j = i
  · subst h
    by_cases hb : j < v.length
    · simp [get?_set_self v hb a, hb]
    · rw [get?_eq_none _ (by simpa [length_set] using Nat.le_of_not_lt hb)]
      simp [hb]
  · simp [get?_set_ne v h a, h]

/-!
## Structural results
-/

/-- Append one element at the end. -/
def push (v : Vec α) (a : α) : Vec α := ⟨v.toList ++ [a]⟩

/-- Remove and return the last element, or `none` when there is none.

`Vec.pop?_push` is the law this exists for: it inverts `Vec.push`. A `Vec` is not
built by cases, so an operation on its end has no other characterisation. -/
def pop? (v : Vec α) : Option (Vec α × α) :=
  v.toList.getLast?.map (fun a => (⟨v.toList.dropLast⟩, a))

@[simp] theorem length_push (v : Vec α) (a : α) : (v.push a).length = v.length + 1 := by
  simp [length, push]

theorem get?_push_lt (v : Vec α) (a : α) {i : Nat} (h : i < v.length) :
    (v.push a).get? i = v.get? i := by
  simp only [get?, push]
  exact List.getElem?_append_left h

@[simp] theorem get?_push_self (v : Vec α) (a : α) : (v.push a).get? v.length = some a := by
  simp [get?, push, length]

@[simp] theorem pop?_empty : (empty : Vec α).pop? = none := rfl

/-- `pop?` inverts `push`. -/
@[simp] theorem pop?_push (v : Vec α) (a : α) : (v.push a).pop? = some (v, a) := by
  simp [pop?, push]

/-- A successful pop shortens by exactly one, and `Vec.pop?_isSome_iff` says when
one succeeds. -/
theorem length_of_pop? {v w : Vec α} {a : α} (h : v.pop? = some (w, a)) :
    v.length = w.length + 1 := by
  simp only [pop?, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, heq⟩ := h
  have hne : v.toList ≠ [] := fun hnil => by simp [hnil] at hb
  have hw : v.toList.dropLast = w.toList := congrArg Array.toList (congrArg Prod.fst heq)
  have hpos : v.toList.length ≠ 0 := by simpa using hne
  simp only [length, ← hw, List.length_dropLast]
  omega

/-- A pop succeeds exactly when there is an element to remove. -/
theorem pop?_isSome_iff (v : Vec α) : v.pop?.isSome = true ↔ v.length ≠ 0 := by
  simp [pop?, length]

/-!
## Composition
-/

/-- Concatenation, in order. -/
def append (v w : Vec α) : Vec α := ⟨v.toList ++ w.toList⟩

instance : Append (Vec α) := ⟨append⟩

/-- The first `n` elements, or all of them when `n` is at least the length. -/
def take (v : Vec α) (n : Nat) : Vec α := ⟨v.toList.take n⟩

/-- All but the first `n` elements. -/
def drop (v : Vec α) (n : Nat) : Vec α := ⟨v.toList.drop n⟩

/-- The prefix/suffix pair at `n`. `Vec.append_splitAt` recovers the original. -/
def splitAt (v : Vec α) (n : Nat) : Vec α × Vec α := (v.take n, v.drop n)

/-- `docs/STDLIB.md` §3's name for keeping a prefix. It is `Vec.take` at this
level; the `OwnedVec` operation of the same name is a different thing, since it
must also account for the dropped elements' destruction obligations. -/
abbrev truncate (v : Vec α) (n : Nat) : Vec α := v.take n

/-- `docs/STDLIB.md` §3's name for the empty result. As with `Vec.truncate`, the
`OwnedVec` operation is a different thing: it releases elements and may retain
capacity. -/
abbrev clear (_ : Vec α) : Vec α := empty

@[simp] theorem toList_append (v w : Vec α) : (v ++ w).toList = v.toList ++ w.toList := rfl

@[simp] theorem length_append (v w : Vec α) : (v ++ w).length = v.length + w.length := by
  simp [length]

theorem get?_append_left {v : Vec α} {i : Nat} (h : i < v.length) (w : Vec α) :
    (v ++ w).get? i = v.get? i := by
  simp only [get?, toList_append]
  exact List.getElem?_append_left h

theorem get?_append_right {v : Vec α} {i : Nat} (h : v.length ≤ i) (w : Vec α) :
    (v ++ w).get? i = w.get? (i - v.length) := by
  simp only [get?, toList_append]
  exact List.getElem?_append_right h

@[simp] theorem empty_append (v : Vec α) : (empty : Vec α) ++ v = v := by
  apply toList_injective
  simp [empty]

@[simp] theorem append_empty (v : Vec α) : v ++ (empty : Vec α) = v := by
  apply toList_injective
  simp [empty]

theorem append_assoc (u v w : Vec α) : (u ++ v) ++ w = u ++ (v ++ w) := by
  apply toList_injective
  simp

@[simp] theorem length_take (v : Vec α) (n : Nat) : (v.take n).length = min n v.length := by
  simp [length, take]

@[simp] theorem length_drop (v : Vec α) (n : Nat) : (v.drop n).length = v.length - n := by
  simp [length, drop]

/-- Splitting loses nothing and reorders nothing. -/
@[simp] theorem append_splitAt (v : Vec α) (n : Nat) : v.take n ++ v.drop n = v := by
  apply toList_injective
  simp [take, drop]

theorem splitAt_eq (v : Vec α) (n : Nat) : v.splitAt n = (v.take n, v.drop n) := rfl

theorem get?_take (v : Vec α) (n i : Nat) :
    (v.take n).get? i = if i < n then v.get? i else none := by
  by_cases h : i < n
  · simp [get?, take, h]
  · simp only [get?, take, h, if_false, List.getElem?_eq_none_iff,
      List.length_take]
    omega

theorem get?_drop (v : Vec α) (n i : Nat) : (v.drop n).get? i = v.get? (n + i) := by
  simp [get?, drop]


/-!
## Prefixes and suffixes

`docs/SPIKE_PROOF_BURDEN.md` classifies four burdens across three spikes as
`library-instance`, and all four are the same shape:
`write_all_loop(payload)` is "standard partial-write induction over the derived
payload suffix", `buffered_stdout(..., committedPrefix)` and
`SliceConsumerInvariant(output, consumed, outLen)` are each a "standard
partial-write consumer", and `crc32_prefix(transferred - remaining)` is a
"standard CRC prefix theorem". The word doing the work in each row is
*standard*: the ledger expects one reusable library theorem, not four authored
proofs.

`docs/STDLIB.md` §6 draws the line for where those live. Machine-state templates
such as `SliceConsumerInvariant` belong to the CFG proof library, because "the
pure library owns ordered-sequence and slice laws, while the CFG layer connects
those laws to selected registers, pointers, provenance, and loans." This section
is the pure half: what a committed prefix and an unwritten suffix are, and how
they behave when a write commits more. Nothing here mentions a register, a
handle, or a byte.

The loop those four share maintains a written count `n` against a payload `v`.
The unwritten suffix is `v.drop n`; the committed prefix is `v.take n`;
`Vec.append_splitAt` says they reconstruct `v` at every step;
`Vec.take_add` says a step of `k` commits exactly the next `k` elements and no
others; and `Vec.length_drop_lt_of_pos` is why the loop terminates.
-/

/-- `v.IsPrefix w` holds when `w` begins with `v`. -/
def IsPrefix (v w : Vec α) : Prop := ∃ rest : Vec α, v ++ rest = w

@[simp] theorem take_zero (v : Vec α) : v.take 0 = empty := by
  apply toList_injective
  simp [take, empty]

@[simp] theorem drop_zero (v : Vec α) : v.drop 0 = v := by
  apply toList_injective
  simp [drop]

@[simp] theorem drop_drop (v : Vec α) (n m : Nat) : (v.drop n).drop m = v.drop (n + m) := by
  apply toList_injective
  simp [drop]

theorem take_take (v : Vec α) (n m : Nat) : (v.take n).take m = v.take (min m n) := by
  apply toList_injective
  simp [take, List.take_take]

/-- The unwritten suffix is empty exactly when everything has been written. This is
the loop's exit test, stated over the sequence rather than over a counter. -/
theorem drop_eq_empty_iff (v : Vec α) (n : Nat) : v.drop n = empty ↔ v.length ≤ n := by
  constructor
  · intro h
    have : v.toList.drop n = [] := congrArg Array.toList h
    exact List.drop_eq_nil_iff.mp this
  · intro h
    apply toList_injective
    simpa [drop, empty] using List.drop_eq_nil_of_le h

/--
A step of `k` commits exactly the next `k` elements.

This is `docs/STDLIB.md` §6's "positive partial writes commit exact prefixes and
retain the unique unwritten suffix", at the sequence level: after `n` written,
writing `k` more extends the committed prefix by `(v.drop n).take k` and by
nothing else.
-/
theorem take_add (v : Vec α) (n k : Nat) :
    v.take (n + k) = v.take n ++ (v.drop n).take k := by
  apply toList_injective
  simp [take, drop, List.take_add]

/-- A positive step strictly shortens the unwritten suffix while any of it remains.
This is the loop variant: without it a provider reporting zero progress would be
indistinguishable from one making progress, which is the `noProgress` outcome
`Spikes/1_Hello_World` gives its own terminal. -/
theorem length_drop_lt_of_pos (v : Vec α) {n k : Nat} (hk : 0 < k) (hn : n < v.length) :
    (v.drop (n + k)).length < (v.drop n).length := by
  simp only [length_drop]
  omega

@[simp] theorem isPrefix_refl (v : Vec α) : v.IsPrefix v := ⟨empty, append_empty v⟩

theorem IsPrefix.trans {u v w : Vec α} (h₁ : u.IsPrefix v) (h₂ : v.IsPrefix w) :
    u.IsPrefix w := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨r₁ ++ r₂, by rw [← append_assoc, hr₁, hr₂]⟩

theorem IsPrefix.length_le {v w : Vec α} (h : v.IsPrefix w) : v.length ≤ w.length := by
  obtain ⟨rest, hrest⟩ := h
  have := congrArg length hrest
  simp only [length_append] at this
  omega

/-- Every committed prefix is a prefix of the whole. -/
theorem take_isPrefix (v : Vec α) (n : Nat) : (v.take n).IsPrefix v :=
  ⟨v.drop n, append_splitAt v n⟩

/-- The committed prefix only grows. This is the conservation property a
partial-write consumer needs: no step can retract what an earlier step
committed. -/
theorem take_isPrefix_take (v : Vec α) {n m : Nat} (h : n ≤ m) :
    (v.take n).IsPrefix (v.take m) := by
  refine ⟨(v.drop n).take (m - n), ?_⟩
  rw [← take_add]
  congr 1
  omega

/-!
## Algebra
-/

/-- Apply `f` to every element, preserving order: `Vec.get?_map`. -/
def map (f : α → β) (v : Vec α) : Vec β := ⟨v.toList.map f⟩

/--
Apply `f` to every element together with its index, preserving order:
`Vec.get?_mapIdx`.

Demanded by the authored spike surface rather than by this plan:
`Spikes/5_Spinning_Cube/Macros.lean` writes `arguments.mapIdx fun index argument
=> ...` to pair call arguments with their Win64 argument locations, which is the
operation's characteristic use — an index-dependent map where the index is a
position in a calling convention.
-/
def mapIdx (f : Nat → α → β) (v : Vec α) : Vec β := ⟨v.toList.mapIdx f⟩

/-- Left fold, in index order. -/
def foldl (f : β → α → β) (init : β) (v : Vec α) : β := v.toList.foldl f init

/-- Right fold, in index order. -/
def foldr (f : α → β → β) (init : β) (v : Vec α) : β := v.toList.foldr f init

/-- Pointwise combination, truncated to the shorter sequence: `Vec.length_zipWith`. -/
def zipWith (f : α → β → γ) (v : Vec α) (w : Vec β) : Vec γ :=
  ⟨v.toList.zipWith f w.toList⟩

@[simp] theorem length_map (f : α → β) (v : Vec α) : (v.map f).length = v.length := by
  simp [length, map]

/-- `map` preserves order and position, which is `docs/STDLIB.md` §5's
"order preservation for append, map, traverse". -/
@[simp] theorem get?_map (f : α → β) (v : Vec α) (i : Nat) :
    (v.map f).get? i = (v.get? i).map f := by
  simp [get?, map]

@[simp] theorem map_empty (f : α → β) : (empty : Vec α).map f = empty := rfl

@[simp] theorem length_mapIdx (f : Nat → α → β) (v : Vec α) :
    (v.mapIdx f).length = v.length := by
  simp [length, mapIdx]

/-- `mapIdx` preserves position, and the index it passes is that position. -/
@[simp] theorem get?_mapIdx (f : Nat → α → β) (v : Vec α) (i : Nat) :
    (v.mapIdx f).get? i = (v.get? i).map (f i) := by
  simp [get?, mapIdx]

/-- `map` is the index-ignoring case of `mapIdx`. -/
theorem mapIdx_const (f : α → β) (v : Vec α) : (v.mapIdx fun _ a => f a) = v.map f := by
  apply ext_of_get?
  intro i
  simp

/-- The composition half of `docs/STDLIB.md` §5's fusion laws. -/
theorem map_map (g : β → γ) (f : α → β) (v : Vec α) :
    (v.map f).map g = v.map (fun a => g (f a)) := by
  apply toList_injective
  simp [map]

theorem map_append (f : α → β) (v w : Vec α) : (v ++ w).map f = v.map f ++ w.map f := by
  apply toList_injective
  simp [map]

@[simp] theorem length_zipWith (f : α → β → γ) (v : Vec α) (w : Vec β) :
    (zipWith f v w).length = min v.length w.length := by
  simp [length, zipWith]

/-- Pointwise combination is pointwise at every index, which is the truncation to
the shorter sequence stated as a law rather than as a length. -/
theorem get?_zipWith (f : α → β → γ) (v : Vec α) (w : Vec β) (i : Nat) :
    (zipWith f v w).get? i = (v.get? i).bind (fun a => (w.get? i).map (f a)) := by
  simp only [get?, zipWith, List.getElem?_zipWith']
  cases v.toList[i]? <;> rfl

@[simp] theorem foldl_empty (f : β → α → β) (init : β) :
    foldl f init (empty : Vec α) = init := rfl

@[simp] theorem foldr_empty (f : α → β → β) (init : β) :
    foldr f init (empty : Vec α) = init := rfl

/-- The recursion law for `foldl`: the last element is folded last. -/
@[simp] theorem foldl_push (f : β → α → β) (init : β) (v : Vec α) (a : α) :
    foldl f init (v.push a) = f (foldl f init v) a := by
  simp [foldl, push]

/-- The recursion law for `foldr`: the last element is folded first. -/
@[simp] theorem foldr_push (f : α → β → β) (init : β) (v : Vec α) (a : α) :
    foldr f init (v.push a) = foldr f (f a init) v := by
  simp [foldr, push]

/-!
## Predicates and search
-/

/-- Whether every element satisfies `p`. -/
def all (p : α → Bool) (v : Vec α) : Bool := v.toList.all p

/-- Whether some element satisfies `p`. -/
def any (p : α → Bool) (v : Vec α) : Bool := v.toList.any p

/-- The first element satisfying `p`, in index order. -/
def find? (p : α → Bool) (v : Vec α) : Option α := v.toList.find? p

/-- Membership as a decidable test. `Vec.Mem` is the propositional form. -/
def contains [BEq α] (v : Vec α) (a : α) : Bool := v.toList.contains a

theorem mem_iff_mem_toList {a : α} {v : Vec α} : a ∈ v ↔ a ∈ v.toList :=
  Array.mem_toList_iff.symm

/--
Membership is occurrence at some index.

This is the law that keeps a consumer off `Vec.toList`. `Vec.mem_iff_mem_toList`
is true but reaches the representation, and the module comment's whole argument
for wrapping `List` is that consumers should not have to.
-/
theorem mem_iff_exists_get? {a : α} {v : Vec α} : a ∈ v ↔ ∃ i, v.get? i = some a :=
  Iff.trans mem_iff_mem_toList List.mem_iff_getElem?

@[simp] theorem not_mem_empty (a : α) : a ∉ (empty : Vec α) := by
  simp [← Array.mem_toList_iff, empty]

theorem all_eq_true_iff (p : α → Bool) (v : Vec α) : v.all p = true ↔ ∀ a ∈ v, p a := by
  simp only [all, List.all_eq_true, mem_iff_mem_toList]

theorem any_eq_true_iff (p : α → Bool) (v : Vec α) : v.any p = true ↔ ∃ a ∈ v, p a := by
  simp only [any, List.any_eq_true, mem_iff_mem_toList]

theorem contains_iff_mem [BEq α] [LawfulBEq α] (v : Vec α) (a : α) :
    v.contains a = true ↔ a ∈ v := by
  simp [contains, ← Array.mem_toList_iff]

/-- A found element is present and satisfies the predicate. The converse direction,
that `find?` returns the *first* such element, needs an index and is left until a
consumer needs it. -/
theorem find?_eq_some {p : α → Bool} {v : Vec α} {a : α} (h : v.find? p = some a) :
    a ∈ v ∧ p a = true :=
  ⟨mem_iff_mem_toList.mpr (List.mem_of_find?_eq_some h), List.find?_some h⟩

/-!
## Positional insertion and removal
-/

/-- Insert `a` so that it lands at index `i`, shifting later elements up. -/
def insertAt (v : Vec α) (i : Nat) (a : α) : Vec α := ⟨v.toList.insertIdx i a⟩

/-- Remove the element at `i`, shifting later elements down. -/
def eraseAt (v : Vec α) (i : Nat) : Vec α := ⟨v.toList.eraseIdx i⟩

theorem length_insertAt (v : Vec α) {i : Nat} (h : i ≤ v.length) (a : α) :
    (v.insertAt i a).length = v.length + 1 := by
  simp [length, insertAt, List.length_insertIdx_of_le_length h]

theorem length_eraseAt (v : Vec α) {i : Nat} (h : i < v.length) :
    (v.eraseAt i).length = v.length - 1 := by
  simp only [length, eraseAt]
  exact List.length_eraseIdx_of_lt h

end Vec

/-!
## Bytes

`docs/STDLIB.md` §1 fixes `ByteArray := Vec Byte`. `Byte` itself is defined in
`Grass/Std/Logical/Byte.lean`, and §1 groups the two; the name is sited here
rather than there only because that module is still under `c-mem`'s declared
temporary custody (`c-mem:1`), and this module's owner does not edit it before
the handoff lands. Merging the two declarations is part of accepting that
handoff and is tracked in `docs/STDLIB_IMPLEMENTATION_PLAN.md`.
-/

/--
The canonical byte container of `docs/STDLIB.md` §1.

**This name collides with Lean's `_root_.ByteArray`.** A module that opens
`Grass.Std.Logical` and then writes a bare `ByteArray` gets an ambiguity error
naming both candidates, so consumers must qualify. That is not a defect in the
collision detection — §1 wants Grass's byte container and Lean's host one to stay
distinct types related by a connection theorem, and an ambiguity error is a
louder version of that than silent shadowing would be. It is a cost of §1's
chosen name, it will be paid by every memory, artifact, and decoder module, and
whether to pay it is the naming question this module's owner has put to the owner
of `docs/STDLIB.md` rather than deciding unilaterally. `Tests/Std/VecVocabulary.lean`
pins both halves: a `List Byte` is rejected here, and so is a host `_root_.ByteArray`.

`ByteSeq` in `Grass/Std/Logical/Byte.lean` is the placeholder this retires. It is
still the type the memory layer's fields use; migrating those uses is a change to
`Grass/Memory/**`, which belongs to `c-mem`, so the two names coexist until that
migration is agreed rather than one being deleted from under its consumers.
-/
abbrev ByteArray := Vec Byte

end Grass.Std.Logical
