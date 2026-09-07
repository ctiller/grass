import Grass.Unsafe.Raw

/-!
# Raw byte emission

Emission is parameterized by an instruction-family encoder and returns either
the complete byte list or an indexed error.  `EmissionError.emptyEncoding`
rejects an empty encoding at the instruction's flattened index.
-/

namespace Grass.Unsafe

universe u v w

/-- External encoder used by the raw emission boundary. -/
structure Encoder (Instruction : Type u) (Byte : Type v) (Error : Type w) where
  encode : Instruction → Except Error (List Byte)

/-- Indexed reason raw emission failed. -/
inductive EmissionError (Error : Type w) where
  | encoder (instructionIndex : Nat) (error : Error)
  | emptyEncoding (instructionIndex : Nat)
deriving Repr, DecidableEq

namespace Encoder

variable {Instruction : Type u} {Byte : Type v} {Error : Type w}

private def emitFrom (encoder : Encoder Instruction Byte Error) :
    Nat → List Instruction → Except (EmissionError Error) (List Byte)
  | _, [] => .ok []
  | index, instruction :: rest =>
      match encoder.encode instruction with
      | .error error => .error (.encoder index error)
      | .ok [] => .error (.emptyEncoding index)
      | .ok bytes =>
          match emitFrom encoder (index + 1) rest with
          | .error error => .error error
          | .ok tail => .ok (bytes ++ tail)

/-- Emit one flat raw instruction list, preserving the first failing index. -/
def emitInstructions (encoder : Encoder Instruction Byte Error)
    (instructions : List Instruction) : Except (EmissionError Error) (List Byte) :=
  emitFrom encoder 0 instructions

/-- Emit the exact flattening of a raw hierarchy. -/
def emit (encoder : Encoder Instruction Byte Error)
    (raw : RawHierarchy Instruction) : Except (EmissionError Error) (List Byte) :=
  encoder.emitInstructions raw.flatten

@[simp] theorem emit_empty (encoder : Encoder Instruction Byte Error) :
    encoder.emit (RawHierarchy.empty : RawHierarchy Instruction) = .ok [] := rfl

end Encoder

end Grass.Unsafe
