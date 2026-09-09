import Grass.Memory.Coordinates

/-! Coordinate regression controls; these establish geometry, not memory access authority. -/
namespace Grass.Tests.Memory.Coordinates
open Grass.Memory Grass.Memory.Coordinates


variable (id other : StorageId)

/-- Different local offsets, same actual bytes: the old loan bypass. -/
example : (Mapping.span ⟨id, 0⟩ ⟨8, 8⟩) =
    (Mapping.span ⟨id, 8⟩ ⟨0, 8⟩) := rfl

/-- Equal local ranges can denote disjoint actual bytes. -/
example : (Mapping.span ⟨id, 0⟩ ⟨0, 8⟩).Disjoint
    (Mapping.span ⟨id, 8⟩ ⟨0, 8⟩) := by
  exact Or.inr (by change (ByteRange.mk 0 8).Disjoint ⟨8, 8⟩; decide)

example (different : id ≠ other) :
    (Mapping.span ⟨id, 0⟩ ⟨0, 8⟩).Disjoint
      (Mapping.span ⟨other, 0⟩ ⟨0, 8⟩) := Or.inl different

/-- Nonzero allocation-local extent starts are preserved, not rebased to zero. -/
example : (resolveRange? ⟨id, 8⟩ ⟨4, 8⟩ 20 ⟨4, 1⟩).isSome = true := by
  rw [resolveRange?_isSome_iff]
  exact ⟨by decide, by change (ByteRange.mk 12 8).WithinBound 20; decide⟩

example : (resolveRange? ⟨id, 8⟩ ⟨4, 8⟩ 19 ⟨4, 1⟩).isSome = false := by
  simp [resolveRange?, ByteRange.Contains, ByteRange.WithinBound,
    ByteRange.shift, ByteRange.stop]

/-- One-past empty positions can resolve, but cover no byte. -/
example : (resolveRange? ⟨id, 8⟩ ⟨0, 8⟩ 16 ⟨8, 0⟩).isSome = true := by
  rw [resolveRange?_isSome_iff]
  exact ⟨by decide, by change (ByteRange.mk 8 8).WithinBound 16; decide⟩

example : ¬ (Mapping.span ⟨id, 8⟩ ⟨8, 0⟩).range.Covers 16 := by
  change ¬ (ByteRange.mk 16 0).Covers 16
  decide


/-- Backing capacity does not permit escape from a view. -/
example : (resolveRange? ⟨id, 8⟩ ⟨4, 8⟩ 64 ⟨3, 1⟩).isSome = false := by
  simp [resolveRange?, ByteRange.Contains, ByteRange.stop]

/-- An empty position past the view also fails containment. -/
example : (resolveRange? ⟨id, 8⟩ ⟨0, 8⟩ 64 ⟨9, 0⟩).isSome = false := by
  simp [resolveRange?, ByteRange.Contains, ByteRange.stop]

/-- Sharing a backing does not make byte overlap transitive. -/
example :
    (Mapping.span ⟨id, 0⟩ ⟨0, 2⟩).Overlaps (Mapping.span ⟨id, 0⟩ ⟨1, 2⟩) ∧
    (Mapping.span ⟨id, 0⟩ ⟨1, 2⟩).Overlaps (Mapping.span ⟨id, 0⟩ ⟨2, 2⟩) ∧
    (Mapping.span ⟨id, 0⟩ ⟨0, 2⟩).Disjoint (Mapping.span ⟨id, 0⟩ ⟨2, 2⟩) := by
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, Or.inr ?_⟩
  · change (ByteRange.mk 0 2).Overlaps ⟨1, 2⟩
    decide
  · change (ByteRange.mk 1 2).Overlaps ⟨2, 2⟩
    decide
  · change (ByteRange.mk 0 2).Disjoint ⟨2, 2⟩
    decide

/-- A loan's empty-position query uses the translated position too. -/
example : (Mapping.span ⟨id, 0⟩ ⟨8, 8⟩).Meets
    (Mapping.span ⟨id, 8⟩ ⟨0, 0⟩) := by
  refine ⟨rfl, ?_⟩
  change (ByteRange.mk 8 8).Meets ⟨8, 0⟩
  decide

end Grass.Tests.Memory.Coordinates

