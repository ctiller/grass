import Grass.Unsafe.Step

/-!
# Raw stepping fixtures

The fixtures pin flattened execution order, first-failure indexing, indexed
single stepping, hierarchy boundaries, and out-of-bounds rejection.
-/

namespace Grass.Tests.Unsafe.Step

open Grass.Unsafe

inductive Instruction where
  | add (amount : Nat)
  | fail
deriving Repr, DecidableEq

inductive Error where
  | fault
deriving Repr, DecidableEq

def stepper : RawStepper Instruction Nat Error where
  step
    | .add amount, state => .ok (state + amount)
    | .fail, _ => .error .fault

def raw : RawHierarchy Instruction := .append
  (.leaf [.add 2])
  (.append (.leaf [.add 3, .add 5]) .empty)

example : raw.flatten = [.add 2, .add 3, .add 5] := by decide
example : stepper.run raw 10 = .ok 20 := by rfl
example : stepper.stepAt raw 1 10 = .ok 13 := by rfl

example : stepper.stepAt raw 3 10 = .error (.outOfBounds 3 3) := by rfl

example : stepper.run (.append (.leaf [.add 2]) (.leaf [.fail, .add 5])) 10 =
    .error (.transition 1 .fault) := by rfl

example : stepper.stepAt (.leaf [.add 2, .fail]) 1 10 =
    .error (.transition 1 .fault) := by rfl

example : stepper.run (.empty : RawHierarchy Instruction) 10 = .ok 10 := by simp

end Grass.Tests.Unsafe.Step
