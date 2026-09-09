import Grass.Std.Logical.Vec

/-! Exact cuts in a represented output, including positions inside an encoding. -/

namespace Grass.Semantics

open Std.Logical

/-- An output cut is a byte position, not a decoded character boundary. -/
structure OutputCut (payload : Vec Byte) where
  offset : Nat
  bounded : offset ≤ payload.length
deriving DecidableEq

namespace OutputCut

variable {payload : Vec Byte}

@[ext] theorem ext {left right : OutputCut payload} (offset : left.offset = right.offset) :
    left = right := by
  cases left
  cases right
  cases offset
  rfl

def zero (payload : Vec Byte) : OutputCut payload := ⟨0, Nat.zero_le _⟩
def full (payload : Vec Byte) : OutputCut payload := ⟨payload.length, Nat.le_refl _⟩

/-- The exact already emitted prefix. -/
def emitted (cut : OutputCut payload) : Vec Byte := payload.take cut.offset

/-- Bytes between two cuts; callers supply ordering when interpreting an advance. -/
def between (before after : OutputCut payload) : Vec Byte :=
  (payload.drop before.offset).take (after.offset - before.offset)

/-- Remaining output belongs to the same payload and exact cut. -/
def remaining (cut : OutputCut payload) : Vec Byte := payload.drop cut.offset

@[simp] theorem length_emitted (cut : OutputCut payload) : cut.emitted.length = cut.offset := by
  simp only [emitted, Vec.length_take, Nat.min_eq_left cut.bounded]

@[simp] theorem emitted_zero : (zero payload).emitted = Vec.empty := by
  simp [emitted, zero]

@[simp] theorem emitted_full : (full payload).emitted = payload := by
  simp [emitted, full]

/-- Every cut conserves the complete rendering. -/
theorem conservation (cut : OutputCut payload) : cut.emitted ++ cut.remaining = payload :=
  Vec.append_splitAt payload cut.offset

/-- Advancing a cut appends exactly the intervening rendered bytes. -/
theorem advance_exact (before after : OutputCut payload) (ordered : before.offset ≤ after.offset) :
    before.emitted ++ before.between after = after.emitted := by
  unfold emitted between
  rw [← Vec.take_add, Nat.add_sub_of_le ordered]

/-- `length_emitted` distinguishes cuts even when the payload repeats bytes. -/
theorem emitted_injective : Function.Injective (emitted (payload := payload)) := by
  intro first second equal
  apply ext
  have lengths := congrArg Vec.length equal
  simpa only [length_emitted] using lengths

/-- Ordered cuts retain their exact byte distance. -/
theorem length_between (before after : OutputCut payload)
    (ordered : before.offset ≤ after.offset) :
    (before.between after).length = after.offset - before.offset := by
  simp only [between, Vec.length_take, Vec.length_drop]
  have bounded := after.bounded
  omega

/-- `advance_exact` makes segmentation irrelevant to the represented bytes. -/
theorem between_compose (first middle last : OutputCut payload)
    (firstMiddle : first.offset ≤ middle.offset) (middleLast : middle.offset ≤ last.offset) :
    first.between middle ++ middle.between last = first.between last := by
  have equal : first.emitted ++ (first.between middle ++ middle.between last) =
      first.emitted ++ first.between last := by
    rw [← Vec.append_assoc, advance_exact first middle firstMiddle,
      advance_exact middle last middleLast, advance_exact first last (Nat.le_trans firstMiddle middleLast)]
  apply Vec.toList_injective
  have lists := congrArg Vec.toList equal
  exact List.append_cancel_left lists

/-- A positive output advance strictly decreases the remaining byte measure. -/
theorem remaining_decreases (before after : OutputCut payload)
    (advance : before.offset < after.offset) :
    after.remaining.length < before.remaining.length := by
  simp only [remaining, Vec.length_drop]
  have bounded := after.bounded
  omega

end OutputCut
end Grass.Semantics
