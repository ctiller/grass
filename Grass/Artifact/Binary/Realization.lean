import Grass.Artifact.Binary.Primitive
import Grass.Grammar.Binary

/-! # Proofs that primitive binary implementations realize Grammar formats -/

namespace Grass.Artifact.Binary

open Grass.Std.Logical Grass.Grammar

/-- The primitive executable parser realizes the generic one-byte language. -/
theorem takeByte_realizes : ParserRealizes anyByteSemantics takeByte := by
  constructor
  · intro input value rest selected
    exact takeByte_writeByte_append value rest ▸ congrArg takeByte selected
  · intro input hint
    cases input with
    | fromList bytes =>
      cases bytes with
      | nil => simp [takeByte, anyByteSemantics, Vec.empty, Vec.get?, eq_comm]
      | cons first tail =>
        simp [takeByte, anyByteSemantics, Vec.empty, Vec.get?]
  · intro input error
    cases input with
    | fromList bytes =>
      cases bytes with
      | nil => simp [takeByte, anyByteSemantics, Vec.get?]
      | cons first tail =>
        simp [takeByte, anyByteSemantics, Vec.get?]
  · intro input value rest success
    exact takeByte_done success

/-- The one-byte writer realizes the same selected language. -/
theorem writeByte_realizes : WriterRealizes anyByteSemantics writeByte := by
  constructor
  · intro value
    exact Derives.byte (fun _ => True) value Vec.empty trivial
  · intro value
    simp [anyByteSemantics, writeByte]

/-- The generic realization theorem specializes to the executable byte
round-trip rather than relying on reduction of the implementation. -/
theorem takeByte_writeByte_via_realization (value : Byte) :
    takeByte (writeByte value) = .done value Vec.empty :=
  parse_write takeByte_realizes writeByte_realizes value

/-- Exact-length parsing into a value whose type retains the checked length. -/
def takeExactSized (count : Nat) (input : Std.Logical.ByteArray) :
    ParseResult (SizedByteArray count) :=
  if enough : count ≤ input.length then
    .done ⟨input.take count, by simp [enough]⟩ (input.drop count)
  else
    .needMore (some (count - input.length))

/-- Writing a sized byte value forgets only its proof, never any byte. -/
def writeExact {count : Nat} (value : SizedByteArray count) :
    Std.Logical.ByteArray :=
  value.1

/-- A sized byte value written in front of any suffix is consumed exactly. -/
@[simp] theorem takeExactSized_writeExact_append {count : Nat}
    (value : SizedByteArray count) (rest : Std.Logical.ByteArray) :
    takeExactSized count (writeExact value ++ rest) = .done value rest := by
  simp [takeExactSized, writeExact, Vec.length_append, value.2,
    Vec.take_append_of_length_eq, Vec.drop_append_of_length_eq]

/-- A short input retains the exact deficit through the sized wrapper. -/
theorem takeExactSized_short {count : Nat} {input : Std.Logical.ByteArray}
    (short : input.length < count) :
    takeExactSized count input = .needMore (some (count - input.length)) := by
  simp [takeExactSized, Nat.not_le.mpr short]

/-- The exact-length consumer realizes the sized fixed-byte format: success,
completeness, and exact short-buffer classification agree with its semantics. -/
theorem takeExactSized_realizes (count : Nat) :
    ParserRealizes (fixedBytesSemantics count) (takeExactSized count) := by
  constructor
  · intro input value rest selected
    subst input
    exact takeExactSized_writeExact_append value rest
  · intro input hint
    by_cases short : input.length < count
    · rw [takeExactSized_short short]
      simp [fixedBytesSemantics, short, eq_comm]
    · have enough : count ≤ input.length := Nat.le_of_not_gt short
      simp [takeExactSized, enough, fixedBytesSemantics, short]
  · intro input error
    by_cases short : input.length < count
    · rw [takeExactSized_short short]
      simp [fixedBytesSemantics]
    · have enough : count ≤ input.length := Nat.le_of_not_gt short
      simp [takeExactSized, enough, fixedBytesSemantics]
  · intro input value rest success
    by_cases short : input.length < count
    · rw [takeExactSized_short short] at success
      contradiction
    · have enough : count ≤ input.length := Nat.le_of_not_gt short
      simp only [takeExactSized, enough, ↓reduceDIte] at success
      injection success with valueEq restEq
      rw [← valueEq, ← restEq]
      exact (Vec.append_splitAt input count).symm

/-- The sized writer realizes the same fixed-byte semantics. -/
theorem writeExact_realizes (count : Nat) :
    WriterRealizes (fixedBytesSemantics count) (@writeExact count) := by
  constructor
  · intro value
    exact Derives.lift (by
      simpa [writeExact, value.2] using anyBytes_derives value.1 Vec.empty)
  · intro value
    simp [fixedBytesSemantics, writeExact]

end Grass.Artifact.Binary
