import Grass.ISA.X86.Bytes

/-! Byte positions computed from instruction sizes. `offset_succ` and
`emitted_length` connect prefix arithmetic to the actual emitted byte sequence. -/
namespace Grass.Assembly.ByteLayout

open Grass.ISA.X86

def offset (sizes : List Nat) (index : Nat) : Nat := (sizes.take index).sum

@[simp] theorem offset_zero (sizes : List Nat) : offset sizes 0 = 0 := by
  simp [offset]

theorem offset_succ (sizes : List Nat) (index : Nat) (h : index < sizes.length) :
    offset sizes (index + 1) = offset sizes index + sizes[index] := by
  unfold offset
  rw [List.take_succ_eq_append_getElem h, List.sum_append]
  simp

@[simp] theorem offset_end (sizes : List Nat) : offset sizes sizes.length = sizes.sum := by
  simp [offset]

theorem offset_le_total (sizes : List Nat) (index : Nat) : offset sizes index ≤ sizes.sum := by
  have h := congrArg List.sum (List.take_append_drop index sizes)
  simp only [List.sum_append] at h
  dsimp [offset]
  omega

theorem item_end_le_total (sizes : List Nat) (index : Nat) (h : index < sizes.length) :
    offset sizes index + sizes[index] ≤ sizes.sum := by
  rw [← offset_succ sizes index h]
  exact offset_le_total sizes (index + 1)

theorem offset_lt_total (sizes : List Nat) (index : Nat) (h : index < sizes.length)
    (positive : 0 < sizes[index]) : offset sizes index < sizes.sum := by
  have bound := item_end_le_total sizes index h
  omega

theorem offset_prepend (before after : List Nat) (index : Nat) :
    offset (before ++ after) (before.length + index) = before.sum + offset after index := by
  induction before with
  | nil => simp
  | cons size rest ih =>
    have h : (size :: rest).length + index = (rest.length + index) + 1 := by
      simp only [List.length_cons]
      omega
    rw [h]
    change (List.take ((rest.length + index) + 1) (size :: (rest ++ after))).sum = _
    rw [List.take_succ_cons, List.sum_cons]
    change size + offset (rest ++ after) (rest.length + index) =
      (size + rest.sum) + offset after index
    rw [ih]
    omega

def sizes (instructions : List InsnEncoding) : List Nat := instructions.map InsnEncoding.size

def emitted (instructions : List InsnEncoding) : Grass.Std.Logical.ByteSeq :=
  instructions.flatMap InsnEncoding.toBytes

theorem emitted_length (instructions : List InsnEncoding) :
    (emitted instructions).length = (sizes instructions).sum := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    simp [emitted, sizes] at ih ⊢

theorem emitted_prefix_length (instructions : List InsnEncoding) (index : Nat) :
    (emitted (instructions.take index)).length = offset (sizes instructions) index := by
  rw [emitted_length]
  simp [sizes, offset]

theorem instruction_size_pos (instructions : List InsnEncoding)
    (size : Nat) (member : size ∈ sizes instructions) : 0 < size := by
  obtain ⟨instruction, _, rfl⟩ := List.mem_map.mp member
  exact instruction.size_pos

end Grass.Assembly.ByteLayout
