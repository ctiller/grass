import Grass.Op.Step
import Grass.Unsafe.Import

/-!
# Executable stepping adapter

`StepAdapter` supplies only the instruction-to-operation and execution-context
inputs needed by `Grass.Op.step`. `stepImported` is definitionally that generic
transition. `stepProgram` threads successful states and stops at the first
rejection while retaining the unattempted imported suffix.
-/

namespace Grass.Unsafe

open Grass.Core Grass.Memory Grass.Op

universe u v w x

/-- Explicit bridge from one decoded instruction type to generic operation input. -/
structure StepAdapter (Instruction : Type u) where
  operation : Instruction → SomeOperation
  context : Instruction → ContextId
  contextKind : Instruction → ContextKind
  cause : Instruction → EventCause
  faultAt : (instruction : Instruction) →
    (sequence : SubstepSequence) → FaultPlan sequence := fun _ _ => .none

/-- Execute one imported instruction through the sole generic transition. -/
def stepImported {Byte : Type v} {Instruction : Type u}
    (adapter : StepAdapter Instruction) (policy : StepPolicy)
    (state : MachineState) (imported : ImportedInstruction Byte Instruction) :
    StepOutcome :=
  Grass.Op.step policy state (adapter.operation imported.instruction)
    (adapter.context imported.instruction)
    (adapter.contextKind imported.instruction)
    (adapter.cause imported.instruction)
    (adapter.faultAt imported.instruction)

/-- `stepImported_exact` exposes that the adapter defines no alternate semantics. -/
@[simp] theorem stepImported_exact {Byte : Type v} {Instruction : Type u}
    (adapter : StepAdapter Instruction) (policy : StepPolicy)
    (state : MachineState) (imported : ImportedInstruction Byte Instruction) :
    stepImported adapter policy state imported =
      Grass.Op.step policy state (adapter.operation imported.instruction)
        (adapter.context imported.instruction)
        (adapter.contextKind imported.instruction)
        (adapter.cause imported.instruction)
        (adapter.faultAt imported.instruction) := rfl

/-- One attempted imported instruction and its generic step outcome. -/
structure StepRecord (Byte : Type v) (Instruction : Type u) where
  imported : ImportedInstruction Byte Instruction
  outcome : StepOutcome

/-- Observable result covering one exact imported instruction sequence. -/
structure StepTrace (Byte : Type v) (Instruction : Type u)
    (input : List (ImportedInstruction Byte Instruction)) where
  records : List (StepRecord Byte Instruction)
  finalState : MachineState
  remaining : List (ImportedInstruction Byte Instruction)
  coverage : records.map StepRecord.imported ++ remaining = input

namespace StepTrace

/-- Imported byte offsets attempted in order. -/
def attemptedOffsets {Byte : Type v} {Instruction : Type u}
    {input : List (ImportedInstruction Byte Instruction)}
    (trace : StepTrace Byte Instruction input) : List Nat :=
  trace.records.map fun record => record.imported.offset

/-- Rejection reasons in the attempted prefix. -/
def rejections {Byte : Type v} {Instruction : Type u}
    {input : List (ImportedInstruction Byte Instruction)}
    (trace : StepTrace Byte Instruction input) : List StepRejection :=
  trace.records.filterMap fun record => record.outcome.rejection?

/-- Imported byte offsets retained after the first rejection. -/
def remainingOffsets {Byte : Type v} {Instruction : Type u}
    {input : List (ImportedInstruction Byte Instruction)}
    (trace : StepTrace Byte Instruction input) : List Nat :=
  trace.remaining.map ImportedInstruction.offset

end StepTrace

private def stepList {Byte : Type v} {Instruction : Type u}
    (adapter : StepAdapter Instruction) (policy : StepPolicy) :
    (state : MachineState) → (input : List (ImportedInstruction Byte Instruction)) →
      StepTrace Byte Instruction input
  | state, [] => ⟨[], state, [], rfl⟩
  | state, imported :: rest =>
      let outcome := stepImported adapter policy state imported
      match outcome with
      | .rejected reason =>
          ⟨[⟨imported, .rejected reason⟩], state, rest, rfl⟩
      | .ran nextState =>
          let tail := stepList adapter policy nextState rest
          ⟨⟨imported, .ran nextState⟩ :: tail.records,
            tail.finalState, tail.remaining, by
              simp only [List.map_cons, List.cons_append]
              rw [tail.coverage]⟩

/-- Step a decoded program in imported order, stopping on first rejection. -/
def stepProgram {CFGState : Type w} {Terminal : Type x}
    {Byte : Type v} {Instruction : Type u}
    (adapter : StepAdapter Instruction) (policy : StepPolicy)
    (state : MachineState)
    (program : ImportedProgram CFGState Terminal Byte Instruction) :
    StepTrace Byte Instruction program.instructions :=
  stepList adapter policy state program.instructions

end Grass.Unsafe
