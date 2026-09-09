import Grass.Memory.ByteStore
import Grass.Memory.Provenance
import Grass.Memory.Range
import Grass.Std.Logical.FiniteMap

/-!
# Backing stores and the views onto them

The storage half of the memory model, written fresh rather than migrated.

`g-design:185` replaced the previous design, in which every allocation owned its own
`ByteStore` and a separate list declared which allocations were "the same storage".
That declaration was an authority-level claim the byte semantics did not implement:
`Tests/Op/StandardLoan.lean`'s `the_alias_is_a_byte_level_fact` stores through
one allocation and reads the old value from the one declared aliased to it.

Here bytes live once per `StorageId`. An allocation is a **view**: a backing identity,
a nonnegative origin into it, and its own extent. Two views onto one backing share
bytes, and `sharing_is_real` below is the theorem the old model could not state --
a write through one view is visible through the other, with nothing propagating it.

This file owns storage and says nothing about authority. Grants, epochs, permissions
and obligations belong to `Grass/Memory/State.lean`, which consumes `View.SharesBacking`
rather than keeping a relation of its own.
-/

namespace Grass.Memory

open Grass.Core Grass.Std.Logical

/--
An allocation's storage: which bytes it looks at, and where it starts in them.

`extent` is the view's own size, in view-local coordinates starting at zero. A local
offset `i` is backing offset `origin + i`, which `ByteRange.translate` states for
ranges.

`origin` is a `Nat`, so a view never begins before its store. Allocation mints a view
at origin zero; only a mapping transition produces a non-zero one. The signed offset
the previous design installed in its alias list is the difference of two origins,
which is why nothing has to declare it.
-/
structure View where
  /-- The bytes this view looks at. -/
  backing : StorageId
  /-- Where the view starts in them. -/
  origin : Nat
  /-- How much of them it covers, from `origin`. -/
  extent : ByteRange
deriving DecidableEq, Repr

namespace View

/-- This view's local range, in its backing store's coordinates. -/
def spanOf (v : View) (r : ByteRange) : ByteRange := ByteRange.translate v.origin r

/-- The whole view, in backing coordinates. -/
def span (v : View) : ByteRange := v.spanOf v.extent

/--
`a.SharesBacking b` holds when two views look at the same bytes.

Equality of identity, decided in one comparison. The relation it replaces was a
bounded transitive closure over a declared list, with a fuel bound equal to the
list's length, a symmetry repair, and six theorems holding it together. None of that
survives, because there is nothing to walk: either two views name the same store or
they do not.
-/
def SharesBacking (a b : View) : Prop := a.backing = b.backing

instance (a b : View) : Decidable (a.SharesBacking b) :=
  inferInstanceAs (Decidable (_ = _))

@[simp] theorem sharesBacking_refl (v : View) : v.SharesBacking v := rfl

theorem sharesBacking_symm {a b : View} (h : a.SharesBacking b) : b.SharesBacking a :=
  h.symm

theorem sharesBacking_trans {a b c : View}
    (hab : a.SharesBacking b) (hbc : b.SharesBacking c) : a.SharesBacking c :=
  hab.trans hbc

end View

/--
The bytes of a memory state: one store per backing identity.

Every byte in the model lives here exactly once. An allocation record names a
`StorageId` and an origin; nothing else holds bytes, so nothing can hold a stale copy
of them.
-/
structure Storage where
  /-- The stores, by identity. -/
  stores : FiniteMap StorageId ByteStore

namespace Storage

/-- No backing storage at all. -/
def empty : Storage := ⟨.empty⟩

/-- What `v` holds at its local `offset`: the byte and whether it counts as
initialized. Both from one lookup, because asking twice is how a value and its
initialization drift apart. -/
def cellAt? (s : Storage) (v : View) (offset : Nat) : Option (Byte × Bool) :=
  (s.stores.lookup v.backing).bind fun store => store.cellAt? (v.origin + offset)

/-- The byte alone. -/
def byteAt? (s : Storage) (v : View) (offset : Nat) : Option Byte :=
  (s.cellAt? v offset).map Prod.fst

/--
Write `bytes` at `v`'s local `start`.

**Through the backing store, at the translated offset.** This is the line that makes
sharing real rather than declared: another view onto the same store reads these bytes
without anything having to propagate them, because there is only one copy.

`initializes` is the access descriptor's `producesInitialized`. A completed write does
not always credit initialization, and `ByteStore` carries that per run, so a
non-initializing write over initialized bytes leaves them uninitialized -- the reading
that refuses rather than the one that admits a program a stricter model would reject.
-/
def write (s : Storage) (v : View) (start : Nat) (bytes : ByteSeq)
    (initializes : Bool) : Storage :=
  match s.stores.lookup v.backing with
  | Option.none => s
  | some store =>
      ⟨s.stores.insert v.backing (store.write (v.origin + start) bytes initializes)⟩

/-- Install a fresh backing store. Allocation's half: a new identity and its bytes. -/
def install (s : Storage) (id : StorageId) (store : ByteStore) : Storage :=
  ⟨s.stores.insert id store⟩

/-! ## The laws

Three, and the first is the one the previous design could not state.
-/

/--
**A write through one view is visible through any view onto the same backing.**

This is what `the_alias_is_a_byte_level_fact` refuted for the old model,
here as a fact. There is no propagation step and no hypothesis relating the two views
beyond their sharing a backing: the write went to the bytes, and both views read the
bytes.

Stated over the store the write landed in, which is where the two views meet. What
each sees at a given local offset is then `ByteStore`'s question and not this file's --
`a` wrote at backing offset `a.origin + start`, `b` reads at `b.origin + offset`, and
whether those coincide is arithmetic on the origins rather than a correspondence
anything declares.
-/
theorem sharing_is_real (s : Storage) {a b : View} (hshare : a.SharesBacking b)
    {store : ByteStore} (hlook : s.stores.lookup a.backing = some store)
    (start : Nat) (bytes : ByteSeq) (initializes : Bool) (offset : Nat) :
    (s.write a start bytes initializes).cellAt? b offset =
      (store.write (a.origin + start) bytes initializes).cellAt? (b.origin + offset) := by
  unfold write cellAt?
  rw [hlook]
  unfold View.SharesBacking at hshare
  rw [← hshare]
  simp [FiniteMap.lookup_insert_self]

/-- **A write to one backing does not disturb another.**

Distinct storage identities are distinct bytes, so framing is free here. The old model
needed this as a lemma about allocation identities *and* an alias set that might
relate them, which is why its statement had a hypothesis this one does not need. -/
theorem write_of_other_backing (s : Storage) {a b : View}
    (hne : ¬ a.SharesBacking b) (start : Nat) (bytes : ByteSeq) (initializes : Bool)
    (offset : Nat) : (s.write a start bytes initializes).cellAt? b offset =
      s.cellAt? b offset := by
  unfold write cellAt?
  unfold View.SharesBacking at hne
  cases hlook : s.stores.lookup a.backing with
  | none => simp
  | some store => simp [FiniteMap.lookup_insert_ne _ (Ne.symm hne)]

/-- **Installing a backing does not disturb the others.** Allocation's framing half. -/
theorem install_of_other_backing (s : Storage) {id : StorageId} {v : View}
    (hne : v.backing ≠ id) (store : ByteStore) (offset : Nat) :
    (s.install id store).cellAt? v offset = s.cellAt? v offset := by
  unfold install cellAt?
  simp [FiniteMap.lookup_insert_ne _ hne]

end Storage

end Grass.Memory
