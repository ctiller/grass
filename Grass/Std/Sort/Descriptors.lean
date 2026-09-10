import Grass.Std.Logical.StableSort
import Grass.Std.Logical.ByteOrder

/-!
# Stable sorting of descriptors into one immutable byte source

`sort?` checks every source range before sorting. Source ordinals are computed
from descriptor positions and retained in the logical result, including when
two descriptors select equal bytes. `decode_sort` connects the actual descriptor
computation to sorting those same decoded occurrences.

This is a logical representation connection. It does not assert LF parser
correctness, memory ownership, machine-width representability, or refinement of
the authored bottom-up merge loops.
-/

namespace Grass.Std.Sort

open Grass.Std.Logical

/-- A byte range in the source, independent of any machine address or layout. -/
structure Descriptor where
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

namespace Descriptor

/-- The entire range, including an empty range at EOF, belongs to the source. -/
def Valid (source : Vec Byte) (descriptor : Descriptor) : Prop :=
  descriptor.offset + descriptor.length ≤ source.length

instance (source : Vec Byte) (descriptor : Descriptor) :
    Decidable (descriptor.Valid source) := inferInstanceAs (Decidable (_ ≤ _))

/-- The selected source bytes; `length_bytes_of_valid` rules out truncation. -/
def bytes (source : Vec Byte) (descriptor : Descriptor) : Vec Byte :=
  (source.drop descriptor.offset).take descriptor.length

@[simp] theorem length_bytes (source : Vec Byte) (descriptor : Descriptor) :
    (descriptor.bytes source).length =
      min descriptor.length (source.length - descriptor.offset) := by
  simp [bytes]

theorem length_bytes_of_valid {source : Vec Byte} {descriptor : Descriptor}
    (valid : descriptor.Valid source) :
    (descriptor.bytes source).length = descriptor.length := by
  simp only [length_bytes]
  unfold Valid at valid
  omega

theorem get?_bytes (source : Vec Byte) (descriptor : Descriptor) (index : Nat) :
    (descriptor.bytes source).get? index =
      if index < descriptor.length then source.get? (descriptor.offset + index) else none := by
  simp [bytes, Vec.get?_take, Vec.get?_drop]

end Descriptor

namespace DescriptorSort

/-- The ordinal is logical source identity; the descriptor remains offset/length. -/
abbrev Occurrence := Nat × Descriptor

/-- Decode one occurrence without discarding its source identity. -/
def decode (source : Vec Byte) (occurrence : Occurrence) : Nat × Vec Byte :=
  (occurrence.1, occurrence.2.bytes source)

/-- Compare values only. Source ordinals are not an extra ordering key. -/
def compare (source : Vec Byte) (left right : Occurrence) : Bool :=
  ByteArray.lexicographicLE (decode source left).2 (decode source right).2

/-- Sort the actual source descriptors, retaining their original positions. -/
def sort (source : Vec Byte) (descriptors : Vec Descriptor) : Vec Occurrence :=
  (descriptors.mapIdx fun ordinal descriptor => (ordinal, descriptor)).stableSort (compare source)

@[simp] theorem length_sort (source : Vec Byte) (descriptors : Vec Descriptor) :
    (sort source descriptors).length = descriptors.length := by
  simp [sort]

theorem get?_sort (source : Vec Byte) (descriptors : Vec Descriptor) (index : Nat) :
    (sort source descriptors).get? index =
      ((descriptors.toList.mapIdx fun ordinal descriptor => (ordinal, descriptor)).mergeSort
        (compare source))[index]? := rfl

/-- `permutation_sort` retains every source occurrence, with its exact descriptor. -/
theorem permutation_sort (source : Vec Byte) (descriptors : Vec Descriptor) :
    (sort source descriptors).Permutation
      (descriptors.mapIdx fun ordinal descriptor => (ordinal, descriptor)) :=
  Vec.permutation_stableSort _ _

/-- Every retained ordinal still selects its exact original descriptor. -/
theorem origin_of_mem_sort {source : Vec Byte} {descriptors : Vec Descriptor}
    {occurrence : Occurrence} (member : occurrence ∈ sort source descriptors) :
    descriptors.get? occurrence.1 = some occurrence.2 := by
  have original := (permutation_sort source descriptors).mem_iff.mp member
  obtain ⟨index, found⟩ := Vec.mem_iff_exists_get?.mp original
  rw [Vec.get?_mapIdx] at found
  obtain ⟨descriptor, sourceFound, mappedEqual⟩ := Option.map_eq_some_iff.mp found
  cases mappedEqual
  exact sourceFound

/-- The decoded values of the output are ordered by unsigned byte comparison. -/
theorem ordered_sort (source : Vec Byte) (descriptors : Vec Descriptor) :
    (sort source descriptors).Pairwise (fun left right => compare source left right = true) := by
  apply Vec.pairwise_stableSort
  · intro _ _ _ first second
    exact ByteArray.lexicographicLE_trans first second
  · intro left right
    simpa only [Bool.or_eq_true, compare] using
      ByteArray.lexicographicLE_total (decode source left).2 (decode source right).2

private theorem indexed_ordered {α β : Type} (view : α → β) (input : Vec α) :
    ((input.mapIdx fun ordinal value => (ordinal, value)).map
      (fun occurrence => (occurrence.1, view occurrence.2))).Pairwise
      (fun left right => left.1 < right.1) := by
  apply (Vec.pairwise_iff_get _).mpr
  intro i j hi hj less
  simpa [Vec.get, Vec.mapIdx, Vec.map] using less

/-- Sorting descriptors and then decoding is exactly sorting decoded occurrences. -/
theorem decode_sort (source : Vec Byte) (descriptors : Vec Descriptor) :
    (sort source descriptors).map (decode source) =
      ((descriptors.mapIdx fun ordinal descriptor => (ordinal, descriptor)).map
        (decode source)).stableSort
        (fun left right => ByteArray.lexicographicLE left.2 right.2) := by
  apply Vec.map_stableSort
  intro _ _ _ _
  rfl

/-- Decoding retains the multiplicity and identity of every source occurrence. -/
theorem decoded_permutation_sort (source : Vec Byte) (descriptors : Vec Descriptor) :
    ((sort source descriptors).map (decode source)).Permutation
      ((descriptors.mapIdx fun ordinal descriptor => (ordinal, descriptor)).map
        (decode source)) := by
  rw [decode_sort]
  exact Vec.permutation_stableSort _ _

/-- The actual decoded output has pairwise unsigned lexicographic order. -/
theorem decoded_ordered_sort (source : Vec Byte) (descriptors : Vec Descriptor) :
    ((sort source descriptors).map (decode source)).Pairwise
      (fun left right => ByteArray.lexicographicLE left.2 right.2 = true) := by
  rw [decode_sort]
  apply Vec.pairwise_stableSort
  · intro _ _ _ first second
    exact ByteArray.lexicographicLE_trans first second
  · intro left right
    simpa only [Bool.or_eq_true] using ByteArray.lexicographicLE_total left.2 right.2

/-- Equal decoded values retain their source-ordinal order at actual output
`idxOf?` positions. The ordinals are computed from the descriptor input. -/
theorem stable_equal_bytes (source : Vec Byte) (descriptors : Vec Descriptor)
    (i j : Nat) (hi : i < descriptors.length) (hj : j < descriptors.length)
    (before : i < j)
    (equal : (descriptors.get i hi).bytes source = (descriptors.get j hj).bytes source)
    {p q : Nat}
    (first : ((sort source descriptors).map (decode source)).idxOf?
      (i, (descriptors.get i hi).bytes source) = some p)
    (second : ((sort source descriptors).map (decode source)).idxOf?
      (j, (descriptors.get j hj).bytes source) = some q) : p < q := by
  rw [decode_sort] at first second
  let input := (descriptors.mapIdx fun ordinal descriptor => (ordinal, descriptor)).map
    (decode source)
  have inputOrdered : input.Pairwise (fun left right => left.1 < right.1) :=
    indexed_ordered (fun descriptor => descriptor.bytes source) descriptors
  have unique : input.toList.Nodup := by
    apply List.Pairwise.imp _ inputOrdered
    intro left right less same
    exact Nat.ne_of_lt less (congrArg Prod.fst same)
  have pair : [(i, (descriptors.get i hi).bytes source),
      (j, (descriptors.get j hj).bytes source)].Sublist input.toList := by
    have hi' : i < input.toList.length := by simpa [input, Vec.map, Vec.mapIdx, Vec.length] using hi
    have hj' : j < input.toList.length := by simpa [input, Vec.map, Vec.mapIdx, Vec.length] using hj
    have selected := List.map_getElem_sublist (l := input.toList)
      (is := [⟨i, hi'⟩, ⟨j, hj'⟩]) (by simp [before])
    have firstExact : input.toList[i]'hi' =
        (i, (descriptors.get i hi).bytes source) := by
      simp [input, decode, Vec.map, Vec.mapIdx, Vec.get] <;> rfl
    have secondExact : input.toList[j]'hj' =
        (j, (descriptors.get j hj).bytes source) := by
      simp [input, decode, Vec.map, Vec.mapIdx, Vec.get] <;> rfl
    simpa only [List.map_cons, List.map_nil, Fin.getElem_fin, firstExact, secondExact] using selected
  apply Vec.stableSort_idxOf?_lt
    (fun left right : Nat × Vec Byte => ByteArray.lexicographicLE left.2 right.2)
    (fun _ _ _ => ByteArray.lexicographicLE_trans)
    (fun left right => by simpa only [Bool.or_eq_true] using
      ByteArray.lexicographicLE_total left.2 right.2)
    unique _ pair first second
  simp [equal]

/-- Out-of-source descriptors are rejected before the sorting computation. -/
def sort? (source : Vec Byte) (descriptors : Vec Descriptor) : Option (Vec Occurrence) :=
  if descriptors.all (fun descriptor => decide (descriptor.Valid source)) then
    some (sort source descriptors)
  else none

theorem sort?_eq_some_iff (source : Vec Byte) (descriptors : Vec Descriptor)
    (output : Vec Occurrence) :
    sort? source descriptors = some output ↔
      (∀ descriptor ∈ descriptors, descriptor.Valid source) ∧
        output = sort source descriptors := by
  unfold sort?
  split
  · rename_i accepted
    have valid : ∀ descriptor ∈ descriptors, descriptor.Valid source := by
      simpa only [Vec.all_eq_true_iff, decide_eq_true_eq] using accepted
    simp only [Option.some.injEq]
    constructor
    · intro same
      exact ⟨valid, same.symm⟩
    · rintro ⟨_, same⟩
      exact same.symm
  · rename_i refused
    have invalid : ¬ (∀ descriptor ∈ descriptors, descriptor.Valid source) := by
      simpa only [Vec.all_eq_true_iff, decide_eq_true_eq] using refused
    simp [invalid]

theorem sort?_eq_none_iff (source : Vec Byte) (descriptors : Vec Descriptor) :
    sort? source descriptors = none ↔
      ¬ (∀ descriptor ∈ descriptors, descriptor.Valid source) := by
  simp [sort?, Vec.all_eq_true_iff]

/-- Successful checking makes every selected output slice exact, not truncated. -/
theorem valid_of_sort?_eq_some {source : Vec Byte} {descriptors : Vec Descriptor}
    {output : Vec Occurrence} (checked : sort? source descriptors = some output)
    {occurrence : Occurrence} (member : occurrence ∈ output) :
    occurrence.2.Valid source := by
  obtain ⟨valid, rfl⟩ := (sort?_eq_some_iff source descriptors output).mp checked
  exact valid occurrence.2 (Vec.mem_iff_exists_get?.mpr
    ⟨occurrence.1, origin_of_mem_sort member⟩)

end DescriptorSort
end Grass.Std.Sort
