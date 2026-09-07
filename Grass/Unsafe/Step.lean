import Grass.Unsafe.Raw

/-!
# Raw instruction stepping

Raw stepping is parameterized by an external one-instruction transition.  It
executes the exact flattening of a raw hierarchy in order and attaches the
flattened instruction index to both lookup and transition failures.
-/

namespace Grass.Unsafe

universe u v w

/-- External transition used by the raw stepping boundary. -/
structure RawStepper (Instruction : Type u) (State : Type v) (Error : Type w) where
  step : Instruction → State → Except Error State

/-- Indexed reason a requested raw step could not complete. -/
inductive RawStepError (Error : Type w) where
  | outOfBounds (instructionIndex instructionCount : Nat)
  | transition (instructionIndex : Nat) (error : Error)
deriving Repr, DecidableEq

namespace RawStepper

variable {Instruction : Type u} {State : Type v} {Error : Type w}

/-- Step one instruction selected by its index in the exact raw flattening. -/
def stepAt (stepper : RawStepper Instruction State Error)
    (raw : RawHierarchy Instruction) (instructionIndex : Nat) (state : State) :
    Except (RawStepError Error) State :=
  match raw.flatten[instructionIndex]? with
  | none => .error (.outOfBounds instructionIndex raw.flatten.length)
  | some instruction =>
      match stepper.step instruction state with
      | .error error => .error (.transition instructionIndex error)
      | .ok next => .ok next

private def runFrom (stepper : RawStepper Instruction State Error) :
    Nat → List Instruction → State → Except (RawStepError Error) State
  | _, [], state => .ok state
  | instructionIndex, instruction :: rest, state =>
      match stepper.step instruction state with
      | .error error => .error (.transition instructionIndex error)
      | .ok next => stepper.runFrom (instructionIndex + 1) rest next

/-- Run a flat instruction list in order, preserving the first failing index. -/
def runInstructions (stepper : RawStepper Instruction State Error)
    (instructions : List Instruction) (initial : State) :
    Except (RawStepError Error) State :=
  stepper.runFrom 0 instructions initial

/-- Run the exact flattening of a raw hierarchy in order. -/
def run (stepper : RawStepper Instruction State Error)
    (raw : RawHierarchy Instruction) (initial : State) :
    Except (RawStepError Error) State :=
  stepper.runInstructions raw.flatten initial

@[simp] theorem run_empty (stepper : RawStepper Instruction State Error) (initial : State) :
    stepper.run (RawHierarchy.empty : RawHierarchy Instruction) initial = .ok initial := rfl

@[simp] theorem stepAt_empty (stepper : RawStepper Instruction State Error)
    (instructionIndex : Nat) (state : State) :
    stepper.stepAt (RawHierarchy.empty : RawHierarchy Instruction) instructionIndex state =
      .error (.outOfBounds instructionIndex 0) := by
  simp [stepAt]

end RawStepper

end Grass.Unsafe
