import Grass.Unsafe.Emit

/-!
# Raw emission fixtures

The fixtures cover hierarchical concatenation, exact byte order, encoder
failure indexing, empty-encoding rejection, and erasure from a verified source.
-/

namespace Grass.Tests.Unsafe.Emit

open Grass Grass.CFG Grass.Construct.Fragment Grass.Unsafe

inductive Instruction where
  | byte (value : UInt8)
  | pair (first second : UInt8)
  | empty
  | invalid
deriving Repr, DecidableEq

inductive Error where
  | invalidInstruction
deriving Repr, DecidableEq

def encoder : Encoder Instruction UInt8 Error where
  encode
    | .byte value => .ok [value]
    | .pair first second => .ok [first, second]
    | .empty => .ok []
    | .invalid => .error .invalidInstruction

def raw : RawHierarchy Instruction := .concat [
  .leaf [.byte 1, .pair 2 3],
  .append (.leaf [.byte 4]) .empty
]

example : raw.flatten = [.byte 1, .pair 2 3, .byte 4] := by decide
example : encoder.emit raw = .ok [1, 2, 3, 4] := by rfl

example : encoder.emit (.leaf [.byte 1, .invalid, .byte 2]) =
    .error (.encoder 1 .invalidInstruction) := by rfl

example : encoder.emit (.leaf [.byte 1, .empty, .byte 2]) =
    .error (.emptyEncoding 1) := by rfl

def exitTag (name : String) : ExitTag := ⟨⟨"test.unsafe", name⟩⟩

def semantics : Semantics Instruction Nat where
  Executes := fun _ before after => before = after

def effects : EffectModel Instruction Nat where
  derive := List.length

def contract : BlockContract Nat where
  requires := fun _ => True
  exits := [⟨exitTag "normal", fun _ => True⟩]

def verified : VerifiedFragment semantics effects contract where
  source := .sequence [.literal [.byte 1], .literal [.pair 2 3]]
  contractWellFormed := by
    simp [contract, BlockContract.WellFormed, BlockContract.wellFormed,
      BlockContract.exitTags]
  effects := 2
  effectsExact := by simp [effects]
  localCorrect := by
    intro before after _ hexec
    subst after
    refine ⟨⟨exitTag "normal", fun _ => True⟩, ?_, trivial, ?_⟩
    · simp [contract]
    · intro candidate hcandidate _
      simp [contract] at hcandidate
      subst candidate
      rfl

example : (RawHierarchy.ofVerified verified).flatten = verified.source.expand := rfl
example : encoder.emit (RawHierarchy.ofVerified verified) = .ok [1, 2, 3] := by rfl

end Grass.Tests.Unsafe.Emit
