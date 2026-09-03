/-!
# Byte ranges

A half-open range of byte offsets within one allocation, with decidable overlap.

Ranges are **offsets, not addresses**. `docs/MEMORY_MODEL.md` §2 makes provenance,
not numerical address, the thing that authorizes an access, so a range is
meaningful only relative to a root allocation.

This module therefore cannot state that two ranges in different allocations never
alias — it carries no allocation identity, and `⟨0,4⟩.Disjoint ⟨0,4⟩` is false
whatever allocations they belong to. That fact lives in `Provenance.SameStorage`.
What is delivered here is the arithmetic of offsets within one allocation.

Offsets are `Nat`, not `BitVec 64`. An offset is bounded by its allocation's size,
not by the machine word, and `Nat` keeps every framing proof free of wraparound
reasoning. The cost is that `Nat` disjointness does not by itself imply
non-aliasing of the corresponding machine addresses: `⟨2^64 - 1, 16⟩` and
`⟨0, 16⟩` are `Disjoint` here while their base-plus-offset addresses would alias
mod 2^64. `WithinBound` is the predicate that rules such ranges out, and M2 owes
the bridge lemma from bounded `Nat` disjointness to `Address` non-aliasing.

The framing lemmas here are the base case of every disjointness argument in the
memory layer: `applyAccess` frames a write against a read exactly when their
ranges are `Disjoint`.

## Empty ranges have positions

`Overlaps` and `Disjoint` are blind to where an empty range sits, because an
empty range covers no offset. `Contains` is deliberately **not**: it compares
extents, so `⟨0,4⟩.Contains (empty 999)` is false while `⟨0,4⟩.Contains (empty 4)`
is true.

That distinction is load-bearing rather than fussy. A zero-size range whose
`start` is the whole point is how this module represents a *position*, and had
`Contains` been defined as "covers every offset `s` covers", every empty range
would be contained in every range and `WithinBound.of_contains` below would be
false.

Do not read `docs/MEMORY_MODEL.md` §5.1 as the authority for that. An earlier
version of this comment cited it as requiring such offsets "to remain
non-dereferenceable but still meaningful as positions", and the second half of that
is not in the corpus: §5.1's sentence is "It never revives an old pointer, and
one-past/end or invalidated offsets remain non-dereferenceable", which is a
restriction, and it is about offsets past an *allocation*. Representing positions
as empty ranges is this module's choice. The corpus authority for a position inside
a lent range being frozen is §3's frozen-fragment bullet, not §5.1.
-/

namespace Grass.Memory

/--
A half-open range `[start, start + size)` of byte offsets within one allocation.

A range with `size = 0` is empty and overlaps nothing, including itself. That is
the right convention for a zero-length access, which `docs/MEMORY_MODEL.md` §4
treats as initializing no bytes, and it is why `Disjoint` below carries explicit
emptiness disjuncts rather than comparing endpoints alone.
-/
structure ByteRange where
  /-- The first offset in the range. -/
  start : Nat
  /-- The number of bytes covered. -/
  size : Nat
deriving DecidableEq, Repr

namespace ByteRange

/-- The offset one past the last byte covered. -/
def stop (r : ByteRange) : Nat := r.start + r.size

/-- The empty range at `start`. -/
def empty (start : Nat) : ByteRange := ⟨start, 0⟩

/-- `r.Covers offset` holds when `offset` lies in `r`. -/
def Covers (r : ByteRange) (offset : Nat) : Prop := r.start ≤ offset ∧ offset < r.stop

/-- `r.IsEmpty` holds when `r` covers no offset. -/
def IsEmpty (r : ByteRange) : Prop := r.size = 0

/-- Two ranges overlap when some offset lies in both. -/
def Overlaps (r s : ByteRange) : Prop := ∃ offset, r.Covers offset ∧ s.Covers offset

/--
Two ranges are disjoint when neither reaches the other.

Stated arithmetically so that it is decidable without deciding an existential.
`disjoint_iff_not_overlaps` proves it agrees with `¬ Overlaps`; the emptiness
disjuncts are exactly what makes that agreement hold.
-/
def Disjoint (r s : ByteRange) : Prop :=
  r.size = 0 ∨ s.size = 0 ∨ r.stop ≤ s.start ∨ s.stop ≤ r.start

/--
`r.Contains s` holds when `s`'s extent lies within `r`'s.

Extent containment, not offset containment: see the module comment. An empty
range is contained only where it actually sits, one-past-the-end included.
-/
def Contains (r s : ByteRange) : Prop := r.start ≤ s.start ∧ s.stop ≤ r.stop

/--
`r.Meets s` holds when `s` is not wholly outside `r`.

Overlap, plus the case `Overlaps` is deliberately blind to. An empty range covers
no offset, so `⟨0,8⟩.Overlaps (empty 4)` is false although offset 4 is squarely
inside `[0,8)` — and a consumer asking "what is outstanding over this position"
with an empty range got the answer "nothing". Review demonstrated that against the
loan map, where it read as exclusive authority over a borrowed byte.

Asymmetric on purpose, and the argument order is load-bearing. `r` is the extent
that owns bytes; `s` is the query. An empty `r` meets nothing, because a range
covering no bytes constrains no position — so an empty grant does not freeze a
live one.

A position one past the end of `r` is *not* met, which `not_meets_stop` states.
It is not a byte of `r`, which is the whole reason; freezing it would freeze the
byte after every grant.
-/
def Meets (r s : ByteRange) : Prop := ¬ r.Disjoint s ∨ (s.IsEmpty ∧ r.Covers s.start)

/--
`r.WithinBound limit` holds when `r` does not reach past `limit`.

Every range used against a real allocation must satisfy this for that
allocation's size, and every range in a numerically addressed space must satisfy
it for that space's address width. Without it, `Nat` arithmetic admits ranges
whose machine addresses would wrap and alias; see the module comment.
-/
def WithinBound (r : ByteRange) (limit : Nat) : Prop := r.stop ≤ limit

/--
The first `count` bytes of `r`, saturating at `r.size`.

This is the shape of a committed prefix: `docs/MEMORY_MODEL.md` §4 says a write
initializes only the bytes it actually completes, and §1 requires a profile to say
which effects survive a faulting substep. Both are prefixes of a named range.
-/
def take (r : ByteRange) (count : Nat) : ByteRange := ⟨r.start, min count r.size⟩

/-!
## Arithmetic characterizations

These are definitional. They exist so that consumers reason through a stable
theorem statement instead of unfolding a definition: `docs/OLEAN_SHARDING.md` §1
requires facts to cross a module boundary as exported theorems, and these
statements are what M2 and the ISA proofs are entitled to rely on even if a
representation below them changes.
-/

theorem covers_def (r : ByteRange) (offset : Nat) :
    r.Covers offset ↔ r.start ≤ offset ∧ offset < r.start + r.size := Iff.rfl

theorem disjoint_def (r s : ByteRange) :
    r.Disjoint s ↔
      r.size = 0 ∨ s.size = 0 ∨
        r.start + r.size ≤ s.start ∨ s.start + s.size ≤ r.start := Iff.rfl

theorem contains_def (r s : ByteRange) :
    r.Contains s ↔ r.start ≤ s.start ∧ s.start + s.size ≤ r.start + r.size := Iff.rfl

theorem isEmpty_def (r : ByteRange) : r.IsEmpty ↔ r.size = 0 := Iff.rfl

theorem withinBound_def (r : ByteRange) (limit : Nat) :
    r.WithinBound limit ↔ r.start + r.size ≤ limit := Iff.rfl

instance (r : ByteRange) (offset : Nat) : Decidable (r.Covers offset) :=
  decidable_of_iff _ (covers_def r offset).symm

instance (r s : ByteRange) : Decidable (r.Disjoint s) :=
  decidable_of_iff _ (disjoint_def r s).symm

instance (r s : ByteRange) : Decidable (r.Contains s) :=
  decidable_of_iff _ (contains_def r s).symm

instance (r : ByteRange) : Decidable r.IsEmpty :=
  decidable_of_iff _ (isEmpty_def r).symm

instance (r : ByteRange) (limit : Nat) : Decidable (r.WithinBound limit) :=
  decidable_of_iff _ (withinBound_def r limit).symm

instance (r s : ByteRange) : Decidable (r.Meets s) :=
  inferInstanceAs (Decidable (¬ _ ∨ (_ ∧ _)))

@[simp] theorem stop_mk (start size : Nat) :
    (ByteRange.mk start size).stop = start + size := rfl

@[simp] theorem start_empty (start : Nat) : (empty start).start = start := rfl

@[simp] theorem size_empty (start : Nat) : (empty start).size = 0 := rfl

@[simp] theorem take_start (r : ByteRange) (count : Nat) :
    (r.take count).start = r.start := rfl

@[simp] theorem take_size (r : ByteRange) (count : Nat) :
    (r.take count).size = min count r.size := rfl

@[simp] theorem take_self (r : ByteRange) : r.take r.size = r := by simp [take]

/-- Build a `Covers` proof from the two bounds. -/
theorem covers_of {r : ByteRange} {offset : Nat} (h₁ : r.start ≤ offset)
    (h₂ : offset < r.start + r.size) : r.Covers offset := ⟨h₁, h₂⟩

@[simp] theorem not_covers_empty (start offset : Nat) : ¬ (empty start).Covers offset := by
  simp [covers_def]

theorem isEmpty_iff_no_cover {r : ByteRange} : r.IsEmpty ↔ ∀ offset, ¬ r.Covers offset := by
  constructor
  · intro h offset hc
    rw [covers_def] at hc
    rw [isEmpty_def] at h
    omega
  · intro h
    have hs := h r.start
    rw [covers_def] at hs
    rw [isEmpty_def]
    omega

/-! ### Meeting a position

`Meets` exists because `Disjoint` answers the wrong question about an empty range.
The six below are what a consumer reasons through. `meets_interior_position` and
`disjoint_interior_position` are the pair that motivated it — the case a consumer
got wrong. `not_meets_stop` and `not_meets_of_isEmpty` are the guards against
over-freezing, which is the other way to get it wrong.
-/

/-- Anything that overlaps, meets. -/
theorem meets_of_not_disjoint {r s : ByteRange} (h : ¬ r.Disjoint s) : r.Meets s :=
  Or.inl h

/-- **A range meets exactly the positions it covers.**

`Meets` is asymmetric and its argument order is load-bearing, so the sentence is
about `r` meeting the position and not the reverse: `(empty offset).Meets r` is
false for every `r`, by `not_meets_of_isEmpty`. -/
@[simp] theorem meets_empty_iff (r : ByteRange) (offset : Nat) :
    r.Meets (empty offset) ↔ r.Covers offset := by
  constructor
  · rintro (hnd | ⟨-, hc⟩)
    · exact absurd (Or.inr (Or.inl rfl)) hnd
    · exact hc
  · intro hc
    exact Or.inr ⟨rfl, hc⟩

/-- **A range meets a position inside it, though it does not overlap it.** The
concrete case review used: offset 4 inside `[0, 8)`. -/
theorem meets_interior_position : (ByteRange.mk 0 8).Meets (empty 4) := by
  simp [covers_def]

/-- And the same pair is `Disjoint`, which is why `Meets` had to be written rather
than the loan map reusing `Disjoint`. -/
theorem disjoint_interior_position : (ByteRange.mk 0 8).Disjoint (empty 4) :=
  Or.inr (Or.inl rfl)

/-- **One past the end is not met.** It is not a byte of `r`, and treating it as
one would freeze the byte after every loan.

`Contains` answers the other way — `contains_empty_iff` puts `empty r.stop` inside
`r` — and the disagreement is deliberate: `Contains` compares extents, which is
what a bounds check wants, and `Meets` asks which bytes a grant covers, which is
what an authority check wants. The position where they differ is now unreachable
from an access, because `AccessDescriptor.WellFormedIn.rangeNonEmpty` refuses a
zero-size access. -/
@[simp] theorem not_meets_stop (r : ByteRange) : ¬ r.Meets (empty r.stop) := by
  simp [covers_def, stop]

/-- **An empty range meets nothing**, whatever `s` is. A grant over no bytes
therefore constrains no position, which is what stops `Meets` turning a zero-byte
grant into a way to freeze live storage — `Tests/Memory/Loans.lean`'s
`a_grant_of_no_bytes_is_refused` is the stronger consequence: such a grant is
refused at issue, because a grant that freezes nothing is decoration. -/
theorem not_meets_of_isEmpty {r s : ByteRange} (h : r.IsEmpty) : ¬ r.Meets s := by
  rw [isEmpty_def] at h
  rintro (hnd | ⟨-, hc⟩)
  · exact hnd (Or.inl h)
  · rw [covers_def] at hc
    omega

theorem disjoint_iff_not_overlaps {r s : ByteRange} : r.Disjoint s ↔ ¬ r.Overlaps s := by
  constructor
  · intro hd ⟨offset, hr, hs⟩
    rw [covers_def] at hr hs
    rw [disjoint_def] at hd
    omega
  · intro hno
    by_cases hd : r.Disjoint s
    · exact hd
    · rw [disjoint_def] at hd
      exact absurd
        ⟨max r.start s.start,
          covers_of (Nat.le_max_left _ _) (by omega),
          covers_of (Nat.le_max_right _ _) (by omega)⟩
        hno

/-- Two ranges that are not disjoint overlap, with an explicit witness. -/
theorem overlaps_of_not_disjoint {r s : ByteRange} (h : ¬ r.Disjoint s) : r.Overlaps s := by
  rw [disjoint_def] at h
  exact ⟨max r.start s.start, covers_of (Nat.le_max_left _ _) (by omega),
    covers_of (Nat.le_max_right _ _) (by omega)⟩

instance (r s : ByteRange) : Decidable (r.Overlaps s) :=
  if h : r.Disjoint s then .isFalse (disjoint_iff_not_overlaps.mp h)
  else .isTrue (overlaps_of_not_disjoint h)

theorem Disjoint.symm {r s : ByteRange} (h : r.Disjoint s) : s.Disjoint r := by
  rw [disjoint_def] at h ⊢
  omega

/--
The framing law. An offset inside one of two disjoint ranges is outside the other,
so an update confined to `s` leaves every byte of `r` alone.
-/
theorem Disjoint.not_covers {r s : ByteRange} (h : r.Disjoint s) {offset : Nat}
    (hr : r.Covers offset) : ¬ s.Covers offset := fun hs =>
  disjoint_iff_not_overlaps.mp h ⟨offset, hr, hs⟩

@[simp] theorem disjoint_empty_left (start : Nat) (s : ByteRange) :
    (empty start).Disjoint s := .inl rfl

@[simp] theorem disjoint_empty_right (r : ByteRange) (start : Nat) :
    r.Disjoint (empty start) := .inr (.inl rfl)

/-- **A container of a non-empty range meets it.** The bridge between the two
relations, in the one direction that holds: `Contains` compares extents and `Meets`
asks about positions, so it needs the contained range to have a position to offer.
Without the hypothesis it is false -- `⟨0,4⟩.Contains (empty 4)` while
`¬ ⟨0,4⟩.Meets (empty 4)`, which is `not_meets_stop`. -/
theorem meets_of_contains {r s : ByteRange} (hc : r.Contains s) (hne : ¬ s.IsEmpty) :
    r.Meets s := by
  refine meets_of_not_disjoint ?_
  obtain ⟨hs, hst⟩ := hc
  have hsize : 0 < s.size := Nat.pos_of_ne_zero (by simpa [IsEmpty] using hne)
  intro hdisj
  rcases hdisj with h | h <;> simp [ByteRange.stop] at * <;> omega

theorem Contains.refl (r : ByteRange) : r.Contains r := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem Contains.trans {r s t : ByteRange} (h₁ : r.Contains s) (h₂ : s.Contains t) :
    r.Contains t := by
  rw [contains_def] at h₁ h₂ ⊢
  omega

/-- Extent containment implies offset containment, which is the form framing
arguments consume. -/
theorem Contains.covers {r s : ByteRange} (h : r.Contains s) {offset : Nat}
    (ho : s.Covers offset) : r.Covers offset := by
  rw [contains_def] at h
  rw [covers_def] at ho ⊢
  omega

/--
Containment transports disjointness inward, which is how a subobject inherits the
framing already established for its parent.
-/
theorem Disjoint.of_contains {r s t : ByteRange} (h : r.Disjoint s) (hc : s.Contains t) :
    r.Disjoint t := by
  rw [disjoint_def] at h ⊢
  rw [contains_def] at hc
  omega

/-- Containment transports a bound inward. -/
theorem WithinBound.of_contains {r s : ByteRange} {limit : Nat}
    (h : r.WithinBound limit) (hc : r.Contains s) : s.WithinBound limit := by
  rw [withinBound_def] at h ⊢
  rw [contains_def] at hc
  omega

/-- A prefix never escapes the range it came from. -/
theorem contains_take (r : ByteRange) (count : Nat) : r.Contains (r.take count) := by
  rw [contains_def]
  simp only [take]
  omega

/-- Anything disjoint from a range is disjoint from each of its prefixes, which is
how framing established for a whole access survives a partial one. -/
theorem Disjoint.of_take {r s : ByteRange} (h : r.Disjoint s) (count : Nat) :
    r.Disjoint (s.take count) := h.of_contains (contains_take s count)

/-- An empty range is contained only where it sits. This is the fact the module
comment turns on, and it is why `WithinBound.of_contains` is provable. -/
theorem contains_empty_iff (r : ByteRange) (start : Nat) :
    r.Contains (empty start) ↔ (r.start ≤ start ∧ start ≤ r.stop) := by
  rw [contains_def]
  simp only [empty, stop]
  omega

end ByteRange

/--
`IsAligned addr align` holds when `addr` is a multiple of `align`.

`align = 1` is how "no alignment demand" is written, and `isAligned_one` proves it
accepts everything. There is deliberately **no** disjunct making `align = 0`
universally true: zero is what an unpopulated `Nat` field holds, and a predicate
that accepted everything at its own default value would be exactly the permissive
fallback `docs/FOUNDATION.md` law 8 forbids. As defined, `align = 0` is
restrictive rather than permissive — `isAligned_zero_iff` shows it admits only
address zero — so a forgotten field fails closed.

This is not a `ByteRange` operation and does not live in its namespace: it
constrains an address, not a range of offsets.
-/
def IsAligned (addr align : Nat) : Prop := addr % align = 0

instance (addr align : Nat) : Decidable (IsAligned addr align) :=
  inferInstanceAs (Decidable (_ = _))

@[simp] theorem isAligned_one (addr : Nat) : IsAligned addr 1 := Nat.mod_one addr

/-- A zero alignment fails closed: it admits only address zero, never everything. -/
theorem isAligned_zero_iff (addr : Nat) : IsAligned addr 0 ↔ addr = 0 := by
  simp [IsAligned]

/--
`IsPowerOfTwo align` holds when `align` is a power of two.

Hardware alignment demands are powers of two, and a profile should require this of
the alignments it admits. It is a separate predicate rather than a condition
inside `IsAligned` because the two say different things, and because a device or
descriptor profile may legitimately demand a non-power-of-two stride.
-/
def IsPowerOfTwo (align : Nat) : Prop := ∃ exponent : Nat, align = 2 ^ exponent

theorem isPowerOfTwo_one : IsPowerOfTwo 1 := ⟨0, rfl⟩

theorem isPowerOfTwo_eight : IsPowerOfTwo 8 := ⟨3, rfl⟩

theorem isPowerOfTwo_sixteen : IsPowerOfTwo 16 := ⟨4, rfl⟩

end Grass.Memory
