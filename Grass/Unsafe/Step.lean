import Grass.Op.Step
import Grass.Unsafe.Construct

/-!
# Explicitly tainted stepping

This adapter pairs a raw x86 encoding with a caller-selected modeled operation
and delegates execution to `Grass.Op.step`. The pairing does not prove that the
operation describes the encoding, so every result adds `.semantics` as its
primary missing check while retaining every check already attached to the raw
instruction.
-/

namespace Grass.Unsafe.Step

open Grass Grass.Core Grass.Memory Grass.Op Grass.Obligation Grass.Unsafe

/-- A generic step outcome together with the raw instruction that selected it. -/
structure Result where
  instruction : Unsafe.Construct.X86Instruction
  outcome : StepOutcome

/-- Re-taint an instruction whose connection to a modeled operation is unchecked. -/
def markSemantics (instruction : Unsafe.Construct.X86Instruction) :
    Unsafe.Construct.X86Instruction :=
  Unsafe.Construct.x86Instruction instruction.value .semantics
    (instruction.taint.primary :: instruction.taint.additional)

/-- Execute only through `Grass.Op.step` and retain the explicitly tainted input. -/
def step (policy : StepPolicy) (state : MachineState)
    (instruction : Unsafe.Construct.X86Instruction) (operation : SomeOperation)
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence :=
      fun _ => .none) : Result :=
  { instruction := markSemantics instruction
    outcome := Grass.Op.step policy state operation context contextKind cause faultAt }

/-- `markSemantics_value` proves semantic re-tainting leaves the encoding unchanged. -/
@[simp] theorem markSemantics_value
    (instruction : Unsafe.Construct.X86Instruction) :
    (markSemantics instruction).value = instruction.value := rfl

/-- `markSemantics_taint` states the exact missing-check account after pairing. -/
@[simp] theorem markSemantics_taint
    (instruction : Unsafe.Construct.X86Instruction) :
    (markSemantics instruction).taint =
      ⟨.semantics, instruction.taint.primary :: instruction.taint.additional⟩ := rfl

/-- `step_outcome` exposes exact agreement with the generic operation stepper. -/
@[simp] theorem step_outcome (policy : StepPolicy) (state : MachineState)
    (instruction : Unsafe.Construct.X86Instruction) (operation : SomeOperation)
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) :
    (step policy state instruction operation context contextKind cause faultAt).outcome =
      Grass.Op.step policy state operation context contextKind cause faultAt := rfl

/-- `step_instruction_taint` proves stepping retains every prior missing check. -/
@[simp] theorem step_instruction_taint (policy : StepPolicy) (state : MachineState)
    (instruction : Unsafe.Construct.X86Instruction) (operation : SomeOperation)
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) :
    (step policy state instruction operation context contextKind cause faultAt).instruction.taint =
      ⟨.semantics, instruction.taint.primary :: instruction.taint.additional⟩ := rfl

/-- `step_retains_primary` carries the prior primary check into the result. -/
theorem step_retains_primary (policy : StepPolicy) (state : MachineState)
    (instruction : Unsafe.Construct.X86Instruction) (operation : SomeOperation)
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) :
    instruction.taint.primary ∈
      (step policy state instruction operation context contextKind cause
        faultAt).instruction.taint.additional := by
  rw [step_instruction_taint]
  exact List.mem_cons_self

/-- `step_retains_additional` carries every prior additional check into the result. -/
theorem step_retains_additional (policy : StepPolicy) (state : MachineState)
    (instruction : Unsafe.Construct.X86Instruction) (operation : SomeOperation)
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence)
    {check : MissingCheck} (h : check ∈ instruction.taint.additional) :
    check ∈ (step policy state instruction operation context contextKind cause
      faultAt).instruction.taint.additional := by
  rw [step_instruction_taint]
  exact List.mem_cons_of_mem _ h

end Grass.Unsafe.Step
