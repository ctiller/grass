import Grass.Grammar.Core

/-!
# Primitive binary readers and writers

Concrete executable consumers live here rather than in `Grass.Grammar`: they
are replaceable implementations of the precious formats and classifications.
They operate on `Grass.Std.Logical.ByteArray`, never the host byte container.
-/

namespace Grass.Artifact.Binary

open Grass.Std.Logical Grass.Grammar

/-- Consume one byte. Empty input is repairable by exactly one byte. -/
def takeByte (input : Std.Logical.ByteArray) : ParseResult Byte :=
  match input.get? 0 with
  | none => .needMore (some 1)
  | some value => .done value (input.drop 1)

/-- Emit one byte in the canonical logical byte container. -/
def writeByte (value : Byte) : Std.Logical.ByteArray := Vec.singleton value

/-- A byte written in front of an arbitrary suffix is consumed with that exact
suffix. This is the prefix law used by sequencing parsers. -/
@[simp] theorem takeByte_writeByte_append (value : Byte) (rest : Std.Logical.ByteArray) :
    takeByte (writeByte value ++ rest) = .done value rest := by
  unfold takeByte writeByte
  rw [Vec.get?_append_left (by simp) rest]
  simp only [Vec.get?_singleton_zero]
  rw [Vec.drop_append_of_length_eq (by simp) rest]

/-- The whole-value round trip is the empty-suffix instance of the prefix law. -/
@[simp] theorem takeByte_writeByte (value : Byte) :
    takeByte (writeByte value) = .done value Vec.empty := by
  simpa using takeByte_writeByte_append value Vec.empty

/-- Every successful byte read consumed exactly the returned leading byte. -/
theorem takeByte_done {input : Std.Logical.ByteArray} {value : Byte}
    {rest : Std.Logical.ByteArray} (success : takeByte input = .done value rest) :
    input = Vec.singleton value ++ rest := by
  cases input with
  | fromList bytes =>
    cases bytes with
    | nil => simp [takeByte, Vec.get?] at success
    | cons first tail =>
      simp only [takeByte, Vec.get?, Vec.drop, List.getElem?_cons_zero] at success
      cases success
      rfl

/-- Exact-length consumption validates the length before taking or dropping.
The deficit is exact and uses natural subtraction, so no host-sized arithmetic
or unchecked index participates. -/
def takeExact (count : Nat) (input : Std.Logical.ByteArray) :
    ParseResult Std.Logical.ByteArray :=
  if count ≤ input.length then
    .done (input.take count) (input.drop count)
  else
    .needMore (some (count - input.length))

/-- An exact-length prefix is returned unchanged and leaves the exact suffix. -/
@[simp] theorem takeExact_append {head : Std.Logical.ByteArray} {count : Nat}
    (length : head.length = count) (rest : Std.Logical.ByteArray) :
    takeExact count (head ++ rest) = .done head rest := by
  simp [takeExact, Vec.length_append, length, Vec.take_append_of_length_eq,
    Vec.drop_append_of_length_eq]

/-- Taking zero bytes succeeds without consuming input, including empty input. -/
@[simp] theorem takeExact_zero (input : Std.Logical.ByteArray) :
    takeExact 0 input = .done Vec.empty input := by
  simp [takeExact]

/-- A short buffer is classified as repairable with its exact deficit. -/
theorem takeExact_short {count : Nat} {input : Std.Logical.ByteArray}
    (short : input.length < count) :
    takeExact count input = .needMore (some (count - input.length)) := by
  simp [takeExact, Nat.not_le.mpr short]

/-- Every successful exact-length consume makes progress by exactly `count` and
preserves all bytes through prefix/suffix recomposition. -/
theorem takeExact_done {count : Nat}
    {input value rest : Std.Logical.ByteArray}
    (success : takeExact count input = .done value rest) :
    value.length = count ∧ value ++ rest = input := by
  simp only [takeExact] at success
  split at success
  next enough =>
    cases success
    exact ⟨by simp [enough], Vec.append_splitAt input count⟩
  next short => contradiction

end Grass.Artifact.Binary
