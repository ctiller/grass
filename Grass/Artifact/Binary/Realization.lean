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
  · intro input error success
    cases input with
    | fromList bytes =>
      cases bytes <;> simp [takeByte, Vec.get?] at success
  · intro input errorClass invalid
    simp [anyByteSemantics] at invalid
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

/-- The exact-length consumer realizes the derived fixed-byte format: success,
completeness, and exact short-buffer classification agree with its semantics. -/
theorem takeExact_realizes (count : Nat) :
    ParserRealizes (fixedBytesSemantics count) (takeExact count) := by
  constructor
  · intro input value rest success
    obtain ⟨lengthEq, recomposes⟩ := takeExact_done success
    exact (fixedBytesSemantics count).selectedSound ⟨recomposes.symm, lengthEq⟩
  · intro input value rest selected
    exact takeExact_append selected.2 rest ▸ congrArg (takeExact count) selected.1
  · intro input hint
    simp only [takeExact]
    split
    next enough =>
      constructor
      · intro impossible
        cases impossible
      · intro repairable
        exact (Nat.not_lt_of_ge enough repairable.1).elim
    next short =>
      simp [fixedBytesSemantics, Nat.lt_of_not_ge short, eq_comm]
  · intro input error
    simp only [takeExact]
    split <;> simp [fixedBytesSemantics]
  · intro input value rest success
    obtain ⟨lengthEq, recomposes⟩ := takeExact_done success
    exact ⟨recomposes.symm, lengthEq⟩

end Grass.Artifact.Binary
