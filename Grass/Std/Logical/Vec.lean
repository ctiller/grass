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
structure Vec (α : Type u) where
  /-- Build a `Vec` from a list in the same order. -/
  fromList ::
  /-- The elements, in order. This is the representation, not an export: laws are
  stated over `Vec.length` and `Vec.get?`. -/
  toList : List α

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

/-- Both directions. A consumer review needed the converse twice while writing a
byte cursor and had to derive it each time; a read failing is exactly a read past
the end. -/
theorem get?_eq_none_iff (v : Vec α) (i : Nat) : v.get? i = none ↔ v.length ≤ i := by
  simp [get?, length]

/-- An emptiness characterisation that reaches `= empty`.
`Vec.isEmpty_iff_length_eq_zero` relates a `Bool` to a `Nat` and stops there. -/
theorem eq_empty_iff_length_eq_zero (v : Vec α) : v = empty ↔ v.length = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply toList_injective
    simpa [empty, length] using List.eq_nil_of_length_eq_zero h

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
  simp only [get?, set, toList_fromList]
  rw [List.getElem?_set_self]
  exact h

theorem get?_set_ne (v : Vec α) {i j : Nat} (h : j ≠ i) (a : α) :
    (v.set i a).get? j = v.get? j := by
  simp only [get?, set, toList_fromList]
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
  simp only [get?, push, toList_fromList]
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
  have hw : v.toList.dropLast = w.toList := congrArg toList (congrArg Prod.fst heq)
  have hpos : v.toList.length ≠ 0 := by simpa using hne
  simp only [length, ← hw, List.length_dropLast]
  omega

/-- A pop succeeds exactly when there is an element to remove. -/
theorem pop?_isSome_iff (v : Vec α) : v.pop?.isSome = true ↔ v.length ≠ 0 := by
  simp [pop?, length, List.getLast?_isSome]

/-!
## Induction

A consumer review built five client modules against this library and reported
that the worst thing in it was the absence of this principle. `Vec.foldl_push`
and `Vec.foldr_push` are advertised as recursion laws, and until now there was no
recursor to run them with: `induction v using Vec.recOnPush` was an unknown
constant, so anyone proving a property of a sequence they *built* — an
accumulator, a writer, an encoder — had to hand-roll snoc induction over
`List.reverse` or give up and work in `List`.

That is the leak this module's whole design exists to prevent, and it was not a
missing law but a missing way to use the laws. The library states plenty about
sequences a consumer was handed and, without this, almost nothing usable about
sequences a consumer makes.

`docs/STDLIB.md` §3 does not list an induction principle, because §3 lists
operations. This is not an operation; it is what makes the operations provable
about.
-/

/--
Induct on a sequence as `empty` or `w.push a`.

The direction matters: `push` is how sequences are built here, so this is the
principle that matches the way consumers construct them. Proved by snoc-induction
over the reversed representation, which is the derivation a consumer would
otherwise write for themselves.
-/
@[elab_as_elim] theorem recOnPush {motive : Vec α → Prop} (v : Vec α)
    (empty : motive empty)
    (push : ∀ (w : Vec α) (a : α), motive w → motive (w.push a)) : motive v := by
  have key : ∀ r : List α, motive (fromList r.reverse) := by
    intro r
    induction r with
    | nil => exact empty
    | cons a t ih =>
      rw [List.reverse_cons]
      exact push (fromList t.reverse) a ih
  cases v with
  | fromList l =>
    have h := key l.reverse
    rwa [List.reverse_reverse] at h

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

/-! `Vec.truncate` and `Vec.clear` exist so that the pure names stay stable while
the `OwnedVec` operations of those names differ. A name kept for stability still
owes a law, or a consumer cannot tell which pure operation it was given. -/

@[simp] theorem truncate_eq_take (v : Vec α) (n : Nat) : v.truncate n = v.take n := rfl

@[simp] theorem length_truncate (v : Vec α) (n : Nat) :
    (v.truncate n).length = min n v.length := by
  simp [truncate, take, length]

@[simp] theorem clear_eq_empty (v : Vec α) : v.clear = (empty : Vec α) := rfl

@[simp] theorem length_clear (v : Vec α) : v.clear.length = 0 := rfl

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
  · simp only [get?, take, toList_fromList, h, if_false, List.getElem?_eq_none_iff,
      List.length_take]
    omega

theorem get?_drop (v : Vec α) (n i : Nat) : (v.drop n).get? i = v.get? (n + i) := by
  simp [get?, drop]

/-!
### Splitting a concatenation

`Vec.take_add` gives the increment of the partial-write story and these give the
split. A consumer review found them missing and reported that the advertised
property was therefore not reachable from this module: twenty lines of
`ext_of_get?` boilerplate had to be written before a single line of frame-parsing
code.
-/

/-- Taking exactly the first part of a concatenation returns it. The frame-reading
law: a length-prefixed payload is recovered by taking its own length. -/
@[simp] theorem take_append (u w : Vec α) : (u ++ w).take u.length = u := by
  apply ext_of_get?
  intro i
  rw [get?_take]
  by_cases h : i < u.length
  · simp only [h, if_true]
    exact get?_append_left h w
  · simp only [h, if_false]
    exact (get?_eq_none u (Nat.le_of_not_lt h)).symm

/-- And dropping it returns the rest. -/
@[simp] theorem drop_append (u w : Vec α) : (u ++ w).drop u.length = w := by
  apply ext_of_get?
  intro i
  rw [get?_drop]
  exact get?_append_right (Nat.le_add_right _ _) w |>.trans (by simp)

/-- Taking the whole sequence is the identity. -/
@[simp] theorem take_length (v : Vec α) : v.take v.length = v := by
  apply toList_injective
  simp [take, length]

/-- Dropping the whole sequence leaves nothing. -/
@[simp] theorem drop_length (v : Vec α) : v.drop v.length = empty := by
  apply toList_injective
  simp [drop, length, empty]


/-!
## Prefixes and suffixes

`docs/SPIKE_PROOF_BURDEN.md` carries six `library-instance` rows. Three of them,
in three different spikes, are the same shape: `write_all_loop(payload)` is
"standard partial-write induction over the derived payload suffix", and
`buffered_stdout(..., committedPrefix)` and
`SliceConsumerInvariant(output, consumed, outLen)` are each a "standard
partial-write consumer". The word doing the work in each row is *standard*: the
ledger expects one reusable library theorem, not three authored proofs. A fourth
row, `crc32_prefix(transferred - remaining)`, indexes the same prefix but is a
"standard CRC prefix theorem", so what it needs beyond this section is a CRC
model rather than more sequence law.

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
    have : v.toList.drop n = [] := congrArg toList h
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
  simp only [get?, zipWith, toList_fromList, List.getElem?_zipWith']
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

/-- `a` occurs in `v`. -/
def Mem (a : α) (v : Vec α) : Prop := a ∈ v.toList

instance : Membership α (Vec α) := ⟨fun v a => Mem a v⟩

theorem mem_iff_mem_toList {a : α} {v : Vec α} : a ∈ v ↔ a ∈ v.toList := Iff.rfl

/-- Membership is decidable, so `by decide` discharges it on concrete data.
`Vec.contains` and `Vec.all_eq_true_iff` existed and a consumer review still had
to route a concrete `∀ x ∈ v, …` goal through `of_decide_eq_true` by hand. -/
instance [DecidableEq α] (a : α) (v : Vec α) : Decidable (a ∈ v) :=
  inferInstanceAs (Decidable (a ∈ v.toList))

/-- And bounded quantification over it, which is the shape a concrete goal
actually takes: `∀ x ∈ v, p x`. -/
instance (p : α → Prop) [DecidablePred p] (v : Vec α) : Decidable (∀ x ∈ v, p x) :=
  inferInstanceAs (Decidable (∀ x ∈ v.toList, p x))

/-- The existential form, likewise. -/
instance (p : α → Prop) [DecidablePred p] (v : Vec α) : Decidable (∃ x ∈ v, p x) :=
  inferInstanceAs (Decidable (∃ x ∈ v.toList, p x))

/--
Membership is occurrence at some index.

This is the law that keeps a consumer off `Vec.toList`. `Vec.mem_iff_mem_toList`
is true but reaches the representation, and the module comment's whole argument
for wrapping `List` is that consumers should not have to.
-/
theorem mem_iff_exists_get? {a : α} {v : Vec α} : a ∈ v ↔ ∃ i, v.get? i = some a :=
  List.mem_iff_getElem?

@[simp] theorem not_mem_empty (a : α) : a ∉ (empty : Vec α) := by
  simp [mem_iff_mem_toList, empty]

theorem all_eq_true_iff (p : α → Bool) (v : Vec α) : v.all p = true ↔ ∀ a ∈ v, p a := by
  simp [all, mem_iff_mem_toList]

theorem any_eq_true_iff (p : α → Bool) (v : Vec α) : v.any p = true ↔ ∃ a ∈ v, p a := by
  simp [any, mem_iff_mem_toList]

theorem contains_iff_mem [BEq α] [LawfulBEq α] (v : Vec α) (a : α) :
    v.contains a = true ↔ a ∈ v := by
  simp [contains, mem_iff_mem_toList]

/-- A found element is present and satisfies the predicate. The converse direction,
that `find?` returns the *first* such element, needs an index and is left until a
consumer needs it. -/
theorem find?_eq_some {p : α → Bool} {v : Vec α} {a : α} (h : v.find? p = some a) :
    a ∈ v ∧ p a = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

/-!
## Instances

`docs/STDLIB.md` §1 says a `Vec`'s "equality and high-level laws are extensional
over length and indexed elements". `Vec.ext_of_get?` is that as a proof rule;
these instances are the same statement as something a program can run and a
tactic can use.

Each is derived through `toList` rather than restated, because `Vec.toList` is
injective (`Vec.toList_injective`) and so every decision procedure on the
representation transports exactly. That is the one place where routing through
the representation is right rather than a leak: an instance is about how values
are compared and displayed, not about what a consumer may assume of them.

`GetElem` is the reason `v[i]` and `v[i]?` work. It is worth having beyond
convenience: `docs/STDLIB.md` §3 asks for both a checked and a bounded accessor,
Lean's indexing notation is exactly that pair, and a container that does not
support it reads as foreign at every use site. `Vec.getElem_eq_get` and
`Vec.getElem?_eq_get?` pin that the notation means the accessors and not some
other thing.
-/

instance [DecidableEq α] : DecidableEq (Vec α) := fun v w =>
  decidable_of_iff (v.toList = w.toList)
    ⟨toList_injective, fun h => by rw [h]⟩

instance [BEq α] : BEq (Vec α) := ⟨fun v w => v.toList == w.toList⟩

instance [BEq α] [LawfulBEq α] : LawfulBEq (Vec α) where
  eq_of_beq h := toList_injective (eq_of_beq h)
  rfl := by
    intro v
    show (v.toList == v.toList) = true
    simp

instance [Repr α] : Repr (Vec α) := ⟨fun v prec => Repr.reprPrec v.toList prec⟩

instance : GetElem (Vec α) Nat α (fun v i => i < v.length) where
  getElem v i h := v.get i h

instance : GetElem? (Vec α) Nat α (fun v i => i < v.length) where
  getElem? v i := v.get? i

instance : LawfulGetElem (Vec α) Nat α (fun v i => i < v.length) where
  getElem?_def v i _ := by
    by_cases h : i < v.length
    · simp [getElem?, getElem, h, get?_eq_some_get v i h]
    · simp [getElem?, h, get?_eq_none v (Nat.le_of_not_lt h)]

@[simp] theorem getElem_eq_get (v : Vec α) (i : Nat) (h : i < v.length) :
    v[i] = v.get i h := rfl

@[simp] theorem getElem?_eq_get? (v : Vec α) (i : Nat) : v[i]? = v.get? i := rfl

/--
`for x in v do …` works.

`docs/STDLIB.md` §3 lists iteration among the observations and this library did
not have it; adversarial review found the gap, which neither the absence list nor
the instances fixture had caught. Iteration is in index order, since it delegates
to the underlying list.
-/
instance {m : Type v → Type w} [Monad m] : ForIn m (Vec α) α where
  forIn v init f := ForIn.forIn v.toList init f

/--
Equality is agreement at every index, as an iff.

This is `Vec.ext_of_get?` in both directions and nothing more. An earlier version
carried a `[DecidableEq α]` binder and a docstring claiming it connected the
`DecidableEq` instance to extensional agreement; adversarial review pointed out
that the statement mentions neither `decide` nor `==`, so the binder was dead and
the claim was unsupported. `Tests/Std/VecInstances.lean` exercises the instances
through `eq_of_beq` and `beq_self_eq_true`, which do reach them.
-/
theorem eq_iff_get?_eq (v w : Vec α) : v = w ↔ ∀ i, v.get? i = w.get? i :=
  ⟨fun h _ => by rw [h], ext_of_get?⟩

/-!
## Flattening and chunking

`docs/STDLIB.md` §3 lists `concat` among the composition operations, and this
module deliberately does not use that name.

In Lean, `List.concat` appends *one element* — it is this library's `Vec.push` —
and flattening is `List.flatten`. §3's word is therefore ambiguous, and taking it
at face value would put a `Vec.concat` in front of consumers that means the
opposite of what a Lean author expects, against this plan's own rule that names
are the expensive thing to change and its own reason for shipping the instances a
Lean author reaches for without thinking. The operation below is `flatten`; the
ambiguity in §3 is raised with the owner of `docs/STDLIB.md` rather than resolved
here by a choice of spelling.

There is a second reason this operation is here at all, and it is what fixes its
laws.

§6 gives `Std.Process.ByteFlow` a contract with a sequence fact inside it:

> Positive partial reads produce nonempty ordered chunks; parsers consume their
> concatenation independent of chunk boundaries.

The process half of that — readiness, EOF, cancellation, backpressure — belongs
to `Std.Process` and waits on the process vocabulary.

The sequence half is smaller than an earlier version of this comment claimed. It
said this section "says what 'independent of chunk boundaries' means", naming
`Vec.chunk_extensional`; that declaration's own docstring now retracts it, and
this paragraph was left asserting the retracted version. What `flatten` supplies
is that the flattening is well defined independent of how the chunks were cut —
the obligation a real chunk-extensionality theorem would discharge, not that
theorem. `docs/PROCESS.md` states the real one over a `StreamingParser`, and it
belongs to `Std.Process`.
-/

/-- Flatten a sequence of sequences, in order. -/
def flatten (chunks : Vec (Vec α)) : Vec α :=
  fromList (chunks.toList.map toList).flatten

@[simp] theorem flatten_empty : flatten (empty : Vec (Vec α)) = empty := rfl

@[simp] theorem flatten_singleton (v : Vec α) : flatten (singleton v) = v := by
  apply toList_injective
  simp [flatten, singleton]

/--
Add up a sequence of counts.

`Vec.length_flatten`'s right-hand side used to be `((chunks.map length).toList).sum`,
which sent every consumer of that law to `Vec.toList` — the leak this module's
whole design is meant to prevent, and the one place it did the leaking itself.
Adversarial review found it. `sum` costs a line because `foldl` already exists.
-/
def sum (v : Vec Nat) : Nat := v.foldl (· + ·) 0

@[simp] theorem sum_empty : sum empty = 0 := rfl

/-- The recursion. `Vec.sum` shipped with no law at all in the same commit that
adopted the coverage rule, and on the right-hand side of `Vec.length_flatten` —
so every consumer of that law received a number it could say nothing about, which
is the leak the rule exists to catch. Adversarial review found it. -/
@[simp] theorem sum_push (v : Vec Nat) (a : Nat) : sum (v.push a) = sum v + a := by
  simp [sum, foldl, push]

theorem sum_append (v w : Vec Nat) : sum (v ++ w) = sum v + sum w := by
  induction w using recOnPush with
  | empty => simp [sum, foldl, empty]
  | push u a ih =>
    have : v ++ u.push a = (v ++ u).push a := by
      apply toList_injective; simp [push]
    rw [this, sum_push, ih, sum_push, Nat.add_assoc]

@[simp] theorem length_flatten (chunks : Vec (Vec α)) :
    (flatten chunks).length = (chunks.map length).sum := by
  simp only [flatten, length, map, toList_fromList, List.length_flatten, List.map_map,
    sum, foldl, List.sum_eq_foldl]
  rfl

/-- Flattening distributes over appending chunk sequences, which is what lets a
reader accumulate chunks without recomputing the whole. -/
@[simp] theorem flatten_append (chunks rest : Vec (Vec α)) :
    flatten (chunks ++ rest) = flatten chunks ++ flatten rest := by
  apply toList_injective
  simp [flatten]

/-- One more chunk appends its elements and nothing else. This is the read-side
counterpart of `Vec.push` and the step law a chunk accumulator needs. -/
@[simp] theorem flatten_push (chunks : Vec (Vec α)) (chunk : Vec α) :
    flatten (chunks.push chunk) = flatten chunks ++ chunk := by
  apply toList_injective
  simp [flatten, push]

/--
Flattening one more chunk reads through to the chunk it came from.

`Vec.flatten` had no indexing law — only length and the append/push recursion —
which adversarial review flagged as the one operation in the module characterised
solely by its recursion. This is the missing observation: past the first chunk,
an index into the flattening is an index into the flattening of the rest.
-/
theorem get?_flatten_cons (chunk : Vec α) (rest : Vec (Vec α)) (i : Nat) :
    (flatten (singleton chunk ++ rest)).get? i =
      if i < chunk.length then chunk.get? i
      else (flatten rest).get? (i - chunk.length) := by
  have hcat : flatten (singleton chunk ++ rest) = chunk ++ flatten rest := by
    rw [flatten_append, flatten_singleton]
  rw [hcat]
  by_cases h : i < chunk.length
  · simp [get?_append_left h, h]
  · simp [get?_append_right (Nat.le_of_not_lt h), h]

/-- `chunks` is a chunking of `v` when it flattens to it. Chunk boundaries are
data about how `v` arrived, not about `v`. -/
def IsChunking (chunks : Vec (Vec α)) (v : Vec α) : Prop := flatten chunks = v

theorem isChunking_singleton (v : Vec α) : IsChunking (singleton v) v := by
  simp [IsChunking]

/--
Two chunkings of the same sequence flatten to the same value, so anything applied
to the flattening agrees on them.

**This is weaker than it may look, and weaker than `docs/PROCESS.md`'s
`ChunkExtensional`.** Adversarial review established the gap and it is recorded
here rather than in a plan, because the docstring is what ships. The proof is two
rewrites and a `refl`; `f` never participates, and the same statement holds with
`Vec.flatten` replaced by any function at all, including ones that *do* see chunk
boundaries such as `Vec.length`. So this does not *stop* a consumer from
observing boundaries — it says that a consumer which has already been written as
a function of the flattening cannot.

`docs/PROCESS.md` §"parser_chunking_invariant" defines `ChunkExtensional` as a
predicate on a `StreamingParser` and pairs it with a real theorem relating
`SameFunctionalByteProjection` to `SameParseResultAndRemainder`, and says
explicitly that "parsers which expose feed-call boundaries or per-feed
diagnostics are not `ChunkExtensional`". An incrementally fed parser is not a
function of `Vec.flatten` and this theorem says nothing about one. That property
belongs to `Std.Process` and waits on the process vocabulary.

What this does supply is the sequence-level obligation such a theorem discharges:
that the flattening is well defined independent of how the chunks were cut.
-/
theorem chunk_extensional {δ : Type v} (f : Vec α → δ) {chunks other : Vec (Vec α)}
    {v : Vec α} (hc : IsChunking chunks v) (ho : IsChunking other v) :
    f (flatten chunks) = f (flatten other) := by
  rw [hc, ho]

/-- Every chunk carries at least one element, which is what `docs/STDLIB.md` §6
means by a *positive* partial read. -/
def AllNonEmpty (chunks : Vec (Vec α)) : Prop := ∀ chunk ∈ chunks, chunk.length ≠ 0

@[simp] theorem allNonEmpty_empty : AllNonEmpty (empty : Vec (Vec α)) := by
  intro chunk hmem
  simp at hmem

/--
Nonempty chunks make progress: `n` of them deliver at least `n` elements.

This is the read-side analogue of `Vec.length_drop_lt_of_pos`, and it is why §6
insists the chunks be nonempty. Without it a provider could return unboundedly
many empty chunks while a reader waited for input that never arrived, and no
length argument would detect it.
-/
theorem length_le_length_flatten {chunks : Vec (Vec α)} (h : AllNonEmpty chunks) :
    chunks.length ≤ (flatten chunks).length := by
  obtain ⟨cs⟩ := chunks
  induction cs with
  | nil => simp [flatten]
  | cons c rest ih =>
    have hc : c.length ≠ 0 := h c (by simp [mem_iff_mem_toList])
    have hrest : AllNonEmpty (fromList rest) := by
      intro chunk hmem
      exact h chunk (by simp [mem_iff_mem_toList] at hmem ⊢; exact Or.inr hmem)
    have := ih hrest
    simp only [flatten, length, toList_fromList, List.map_cons, List.flatten_cons,
      List.length_cons, List.length_append] at *
    omega

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
  simp only [length, eraseAt, toList_fromList]
  exact List.length_eraseIdx_of_lt h

/-!
### Where the elements go

The index-shifting laws. `docs/STDLIB.md` §3 lists `insert` and `erase` among the
pure structural results, so unlike an undemanded operation these cannot simply be
withdrawn — but until now they carried only length laws, and adversarial review
compiled an `insertAt` that ignores its index and an `eraseAt` that always drops
the last element, both satisfying everything the module said about them. These
are what say where the elements actually go.
-/

/-- Below the insertion point, nothing moves. -/
theorem get?_insertAt_lt (v : Vec α) {i j : Nat} (h : j < i) (a : α) :
    (v.insertAt i a).get? j = v.get? j :=
  List.getElem?_insertIdx_of_lt h

/-- At the insertion point, the new element, provided the position was reachable. -/
theorem get?_insertAt_self (v : Vec α) (i : Nat) (a : α) :
    (v.insertAt i a).get? i = if i ≤ v.length then some a else none :=
  List.getElem?_insertIdx_self

/-- Above it, everything shifts up by one. -/
theorem get?_insertAt_gt (v : Vec α) {i j : Nat} (h : i < j) (a : α) :
    (v.insertAt i a).get? j = v.get? (j - 1) :=
  List.getElem?_insertIdx_of_gt h

/-- Below the erased position, nothing moves. -/
theorem get?_eraseAt_lt (v : Vec α) {i j : Nat} (h : j < i) :
    (v.eraseAt i).get? j = v.get? j :=
  List.getElem?_eraseIdx_of_lt h

/-- At or above it, everything shifts down by one. -/
theorem get?_eraseAt_ge (v : Vec α) {i j : Nat} (h : i ≤ j) :
    (v.eraseAt i).get? j = v.get? (j + 1) :=
  List.getElem?_eraseIdx_of_ge h

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
