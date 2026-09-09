import Grass.Memory.Range
import Grass.Memory.StorageId

/-! Checked coordinates for contiguous allocation views. This is pure spatial arithmetic, not a MemoryState access gate.
The production adapter must additionally check allocation/backing existence,
live provenance, generation, and mapping stability. No permission is granted here.
Capacity must come from authoritative backing metadata at that boundary. -/
namespace Grass.Memory.Coordinates
open Grass.Memory Grass.Core


/-- Project these fields from an allocation record; do not store a second extent. -/
structure Mapping where
  backing : StorageId
  origin : Nat
deriving DecidableEq, Repr

structure BackingSpan where
  backing : StorageId
  range : ByteRange
deriving DecidableEq, Repr

def Mapping.span (mapping : Mapping) (range : ByteRange) : BackingSpan :=
  ⟨mapping.backing, range.shift mapping.origin⟩

def BackingSpan.Overlaps (a b : BackingSpan) : Prop :=
  a.backing = b.backing ∧ a.range.Overlaps b.range
def BackingSpan.Contains (a b : BackingSpan) : Prop :=
  a.backing = b.backing ∧ a.range.Contains b.range
def BackingSpan.Meets (a b : BackingSpan) : Prop :=
  a.backing = b.backing ∧ a.range.Meets b.range
def BackingSpan.Disjoint (a b : BackingSpan) : Prop :=
  a.backing ≠ b.backing ∨ a.range.Disjoint b.range

instance (a b : BackingSpan) : Decidable (a.Overlaps b) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (a b : BackingSpan) : Decidable (a.Contains b) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (a b : BackingSpan) : Decidable (a.Meets b) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (a b : BackingSpan) : Decidable (a.Disjoint b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Capacity belongs to the backing, and need not equal initialized-cell count. -/
structure ResolvedRange (mapping : Mapping) (extent : ByteRange)
    (capacity : Nat) (requested : ByteRange) : Type where
  withinView : extent.Contains requested
  viewWithinBacking : (extent.shift mapping.origin).WithinBound capacity

def resolveRange? (mapping : Mapping) (extent : ByteRange)
    (capacity : Nat) (requested : ByteRange) :
    Option (ResolvedRange mapping extent capacity requested) :=
  if h : extent.Contains requested ∧
      (extent.shift mapping.origin).WithinBound capacity then
    some ⟨h.1, h.2⟩
  else none

theorem resolveRange?_isSome_iff (mapping : Mapping) (extent : ByteRange)
    (capacity : Nat) (requested : ByteRange) :
    (resolveRange? mapping extent capacity requested).isSome = true ↔
      extent.Contains requested ∧
        (extent.shift mapping.origin).WithinBound capacity := by
  simp only [resolveRange?]
  split <;> simp_all

def ResolvedRange.span {m : Mapping} {e : ByteRange} {c : Nat} {r : ByteRange}
    (_resolved : ResolvedRange m e c r) : BackingSpan := m.span r

theorem ResolvedRange.span_bounded {m : Mapping} {e : ByteRange}
    {c : Nat} {r : ByteRange} (resolved : ResolvedRange m e c r) :
    resolved.span.range.WithinBound c := by
  exact resolved.viewWithinBacking.of_contains
    ((ByteRange.shift_contains_iff e r m.origin).mpr resolved.withinView)

theorem Mapping.span_covers (m : Mapping) (r : ByteRange) (i : Nat) :
    (m.span r).range.Covers (m.origin + i) ↔ r.Covers i := by
  simp only [span, ByteRange.shift, ByteRange.covers_def]
  omega

theorem Mapping.span_size (m : Mapping) (r : ByteRange) :
    (m.span r).range.size = r.size := rfl

theorem Mapping.span_contains_iff (m : Mapping) (r s : ByteRange) :
    (m.span r).Contains (m.span s) ↔ r.Contains s := by
  simp only [BackingSpan.Contains, span, true_and,
    ByteRange.shift_contains_iff]

theorem Mapping.span_disjoint_iff (m : Mapping) (r s : ByteRange) :
    (m.span r).Disjoint (m.span s) ↔ r.Disjoint s := by
  simp only [BackingSpan.Disjoint, span, ne_eq, not_true_eq_false, false_or,
    ByteRange.shift_disjoint_iff]

theorem BackingSpan.disjoint_iff_not_overlaps (a b : BackingSpan) :
    a.Disjoint b ↔ ¬ a.Overlaps b := by
  simp only [Disjoint, Overlaps, ByteRange.disjoint_iff_not_overlaps]
  by_cases h : a.backing = b.backing <;> simp [h]

theorem Mapping.span_meets_iff (m : Mapping) (r s : ByteRange) :
    (m.span r).Meets (m.span s) ↔ r.Meets s := by
  simp only [BackingSpan.Meets, span, true_and]
  change ((r.shift m.origin).Meets (s.shift m.origin)) ↔ r.Meets s
  unfold ByteRange.Meets
  rw [ByteRange.shift_disjoint_iff]
  have covered : (r.shift m.origin).Covers (s.shift m.origin).start ↔
      r.Covers s.start := m.span_covers r s.start
  rw [covered]
  rfl

/-- Derive a prefix without looking up a mapping again. This saturates like
`ByteRange.take`; it does not validate fault plans, committed counts, or atomic
footprints. Those checks remain required at the access boundary. -/
def ResolvedRange.prefix {m : Mapping} {e : ByteRange} {c : Nat}
    {r : ByteRange} (resolved : ResolvedRange m e c r) (count : Nat) :
    ResolvedRange m e c (r.take count) :=
  ⟨resolved.withinView.trans (r.contains_take count), resolved.viewWithinBacking⟩

theorem ResolvedRange.prefix_span {m : Mapping} {e : ByteRange} {c : Nat}
    {r : ByteRange} (resolved : ResolvedRange m e c r) (count : Nat) :
    (resolved.prefix count).span.range = resolved.span.range.take count := rfl

/-- Transport only across equal mapping metadata, not arbitrary new state. -/
def ResolvedRange.transport {m m' : Mapping} {e e' : ByteRange}
    {c c' : Nat} {r : ByteRange} (resolved : ResolvedRange m e c r)
    (hm : m = m') (he : e = e') (hc : c = c') :
    ResolvedRange m' e' c' r := hm ▸ he ▸ hc ▸ resolved


end Grass.Memory.Coordinates

