import Grass.Artifact.Binary.Primitive
import Grass.Grammar.Realization

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

end Grass.Artifact.Binary
