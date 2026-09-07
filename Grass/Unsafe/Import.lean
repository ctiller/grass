import Grass.Unsafe.Raw

/-!
# Raw byte import

A successful one-instruction decode carries the exact nonempty byte prefix it
consumed and the remaining suffix.  Recursive import therefore progresses by a
kernel-checked length decrease and cannot silently skip, duplicate, or retain
input bytes.
-/

namespace Grass.Unsafe

universe u v w

/-- One decoded instruction tied to the exact input bytes it consumed. -/
structure DecodedOne {Byte : Type v} (Instruction : Type u) (input : List Byte) where
  instruction : Instruction
  consumed : List Byte
  rest : List Byte
  consumedNonempty : consumed ≠ []
  inputExact : input = consumed ++ rest

/-- External one-instruction decoder used by raw import. -/
structure Decoder (Byte : Type v) (Instruction : Type u) (Error : Type w) where
  decode : (input : List Byte) → Except Error (DecodedOne Instruction input)

/-- Indexed reason raw import failed. -/
structure ImportError (Error : Type w) where
  byteOffset : Nat
  error : Error
deriving Repr, DecidableEq

namespace Decoder

variable {Byte : Type v} {Instruction : Type u} {Error : Type w}

private def importFrom (decoder : Decoder Byte Instruction Error) (offset : Nat) :
    (input : List Byte) → Except (ImportError Error) (List Instruction)
  | [] => .ok []
  | head :: tail =>
      match _decodedResult : decoder.decode (head :: tail) with
      | .error error => .error ⟨offset, error⟩
      | .ok decoded =>
          match importFrom decoder (offset + decoded.consumed.length) decoded.rest with
          | .error error => .error error
          | .ok tail => .ok (decoded.instruction :: tail)
termination_by input => input.length
decreasing_by
  have consumedPositive : 0 < decoded.consumed.length :=
    by
      cases consumed : decoded.consumed with
      | nil => exact False.elim (decoded.consumedNonempty consumed)
      | cons head tail => simp
  have shorter : decoded.rest.length < decoded.consumed.length + decoded.rest.length :=
    Nat.lt_add_of_pos_left consumedPositive
  have exactLength := congrArg List.length decoded.inputExact
  have inputLength : (head :: tail).length =
      decoded.consumed.length + decoded.rest.length := by
    simpa [List.length_append] using exactLength
  rw [inputLength]
  exact shorter

/-- Decode all bytes into one raw instruction leaf, or return the first failing
byte offset. -/
def importRaw (decoder : Decoder Byte Instruction Error) (bytes : List Byte) :
    Except (ImportError Error) (RawHierarchy Instruction) :=
  match importFrom decoder 0 bytes with
  | .error error => .error error
  | .ok [] => .ok .empty
  | .ok instructions@(_ :: _) => .ok (.leaf instructions)

@[simp] theorem importRaw_empty (decoder : Decoder Byte Instruction Error) :
    decoder.importRaw [] = .ok .empty := by
  unfold importRaw
  rw [importFrom]

end Decoder

end Grass.Unsafe
