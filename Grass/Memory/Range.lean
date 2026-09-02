/-!
# Byte ranges

A half-open range of byte offsets within one allocation, with decidable overlap.

Ranges are allocation-relative rather than absolute, because `docs/MEMORY_MODEL.md`
§2 makes provenance, not numerical address, the thing that authorizes an access.
Two ranges in different allocations never overlap however their machine addresses
compare, and that fact must not be expressible as an accident of arithmetic.

The framing lemmas here are the base case of every disjointness argument in the
memory layer: `applyAccess` frames a write against a read exactly when their
ranges are `Disjoint`.
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

/-- `r.Contains s` holds when every offset of `s` lies in `r`. -/
def Contains (r s : ByteRange) : Prop := ∀ offset, s.Covers offset → r.Covers offset

/-!
## Arithmetic characterizations

These are definitional, and exist so that `omega` can see through the
predicates. Consumers should reason through the named lemmas below rather than
unfolding these in application proofs.
-/

theorem covers_def (r : ByteRange) (offset : Nat) :
    r.Covers offset ↔ r.start ≤ offset ∧ offset < r.start + r.size := Iff.rfl

theorem disjoint_def (r s : ByteRange) :
    r.Disjoint s ↔
      r.size = 0 ∨ s.size = 0 ∨
        r.start + r.size ≤ s.start ∨ s.start + s.size ≤ r.start := Iff.rfl

theorem isEmpty_def (r : ByteRange) : r.IsEmpty ↔ r.size = 0 := Iff.rfl

instance (r : ByteRange) (offset : Nat) : Decidable (r.Covers offset) :=
  decidable_of_iff _ (covers_def r offset).symm

instance (r s : ByteRange) : Decidable (r.Disjoint s) :=
  decidable_of_iff _ (disjoint_def r s).symm

instance (r : ByteRange) : Decidable r.IsEmpty :=
  decidable_of_iff _ (isEmpty_def r).symm

@[simp] theorem stop_mk (start size : Nat) :
    (ByteRange.mk start size).stop = start + size := rfl

@[simp] theorem start_empty (start : Nat) : (empty start).start = start := rfl

@[simp] theorem size_empty (start : Nat) : (empty start).size = 0 := rfl

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

theorem Disjoint.symm {r s : ByteRange} (h : r.Disjoint s) : s.Disjoint r := by
  rw [disjoint_def] at h ⊢
  omega

/--
The framing law. An offset inside one of two disjoint ranges is outside the
other, so an update confined to `s` leaves every byte of `r` alone.
-/
theorem Disjoint.not_covers {r s : ByteRange} (h : r.Disjoint s) {offset : Nat}
    (hr : r.Covers offset) : ¬ s.Covers offset := fun hs =>
  disjoint_iff_not_overlaps.mp h ⟨offset, hr, hs⟩

@[simp] theorem disjoint_empty_left (start : Nat) (s : ByteRange) :
    (empty start).Disjoint s := .inl rfl

@[simp] theorem disjoint_empty_right (r : ByteRange) (start : Nat) :
    r.Disjoint (empty start) := .inr (.inl rfl)

theorem Contains.refl (r : ByteRange) : r.Contains r := fun _ h => h

theorem Contains.trans {r s t : ByteRange} (h₁ : r.Contains s) (h₂ : s.Contains t) :
    r.Contains t := fun offset h => h₁ offset (h₂ offset h)

/--
Containment transports disjointness inward, which is how a subobject inherits
the framing already established for its parent.
-/
theorem Disjoint.of_contains {r s t : ByteRange} (h : r.Disjoint s) (hc : s.Contains t) :
    r.Disjoint t := by
  rw [disjoint_iff_not_overlaps]
  rintro ⟨offset, hr, ht⟩
  exact h.not_covers hr (hc offset ht)

/--
`IsAligned addr align` holds when `addr` is a multiple of `align`.

An alignment of zero is unconstrained, matching a profile that declares no
alignment demand for an access.
-/
def IsAligned (addr align : Nat) : Prop := align = 0 ∨ addr % align = 0

instance (addr align : Nat) : Decidable (IsAligned addr align) :=
  inferInstanceAs (Decidable (_ ∨ _))

@[simp] theorem isAligned_one (addr : Nat) : IsAligned addr 1 := .inr (Nat.mod_one addr)

end ByteRange

end Grass.Memory
