import Grass.Assembly.Store32
import Grass.Op.Step

/-! Bind one resolved Store32 value to the existing transition's oracle seam. -/
namespace Grass.Assembly.Store32Execution

open Grass.Core Grass.Memory Grass.Op
open Grass.Assembly.Store32

/-- A complete answer for the exact write-only descriptor and resolved bytes. -/
def complete (resolved : Resolved) (descriptor : AccessDescriptor)
    (hrange : descriptor.range = resolved.range)
    (hintent : descriptor.intent = .write) : CompleteCommitted descriptor :=
  { committed :=
      { observed := none
        written := some resolved.writeBytes
        observedPresent := by simp [hintent, AccessIntent.write]
        observedAbsent := by simp
        writtenPresent := by simp [hintent, AccessIntent.write]
        writtenAbsent := by simp [hintent, AccessIntent.write]
        observedFits := by simp
        writtenFits := by
          intro bytes h
          cases h
          simp [Store32.Resolved.writeBytes, Store32.Resolved.range, hrange] }
    readsFull := by simp [Committed.readCount, hintent, AccessIntent.write]
    writesFull := by
      intro _
      simp [Committed.writeCount, Store32.Resolved.writeBytes, Store32.Resolved.range,
        hrange] }

/-- An instruction-scoped oracle: it answers the one certified descriptor and
fails closed for every other descriptor. -/
def oracle (resolved : Resolved) (descriptor : AccessDescriptor)
    (hrange : descriptor.range = resolved.range)
    (hintent : descriptor.intent = .write) : Oracle where
  answerResolved _ asked _ :=
    if h : asked = descriptor then
      some (h ▸ complete resolved descriptor hrange hintent)
    else none

/-- Replace only the oracle of an existing policy. All admission, safety,
authority, fault, and event machinery remains the original policy's. -/
private def exactPolicy (base : StepPolicy) (resolved : Resolved) (descriptor : AccessDescriptor)
    (hrange : descriptor.range = resolved.range)
    (hintent : descriptor.intent = .write) : StepPolicy :=
  { base with oracle := oracle resolved descriptor hrange hintent }

/-- The operation family mechanically derived from the one certified descriptor. -/
structure Operation where
  descriptor : AccessDescriptor

instance : HasOperationFacets Operation where
  facets operation :=
    { memoryEffects := some (.single operation.descriptor)
      faults := some operation.descriptor.admittedFaults
      restartability := some operation.descriptor.restartability
      ordering := some operation.descriptor.ordering }

/-- Package the derived one-access operation. -/
def operation (descriptor : AccessDescriptor) : SomeOperation :=
  SomeOperation.of (Operation.mk descriptor)

@[simp] theorem operation_facets (descriptor : AccessDescriptor) :
    (operation descriptor).facets =
      { memoryEffects := some (.single descriptor)
        faults := some descriptor.admittedFaults
        restartability := some descriptor.restartability
        ordering := some descriptor.ordering } := rfl

/-- Execute exactly the descriptor whose complete answer is bound to `resolved`. -/
def step (base : StepPolicy) (state : MachineState) (resolved : Resolved)
    (descriptor : AccessDescriptor) (hrange : descriptor.range = resolved.range)
    (hintent : descriptor.intent = .write) (contextKind : ContextKind)
    (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none) :
    StepOutcome :=
  Grass.Op.step (exactPolicy base resolved descriptor hrange hintent) state
    (operation descriptor) descriptor.context contextKind cause faultAt

theorem step_eq (base : StepPolicy) (state : MachineState) (resolved : Resolved)
    (descriptor : AccessDescriptor) (hrange : descriptor.range = resolved.range)
    (hintent : descriptor.intent = .write) (contextKind : ContextKind)
    (cause : EventCause) (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) :
    step base state resolved descriptor hrange hintent contextKind cause faultAt =
      Grass.Op.step (exactPolicy base resolved descriptor hrange hintent) state
        (operation descriptor) descriptor.context contextKind cause faultAt := rfl

@[simp] theorem oracle_answer_self (resolved : Resolved) (descriptor : AccessDescriptor)
    (hrange : descriptor.range = resolved.range) (hintent : descriptor.intent = .write)
    (state : MachineState) (hadmitted : denialOf state.memory descriptor = none) :
    (oracle resolved descriptor hrange hintent).answer state descriptor =
      some (complete resolved descriptor hrange hintent) := by
  obtain ⟨access, hprepared⟩ := (denialOf_eq_none_iff state.memory descriptor).1 hadmitted
  simp [Oracle.answer, hprepared, oracle]

theorem oracle_answer_ne (resolved : Resolved) (descriptor asked : AccessDescriptor)
    (hrange : descriptor.range = resolved.range) (hintent : descriptor.intent = .write)
    (hne : asked ≠ descriptor) (state : MachineState) :
    (oracle resolved descriptor hrange hintent).answer state asked = none := by
  unfold Oracle.answer
  split <;> simp [oracle, hne]

@[simp] theorem complete_written (resolved : Resolved) (descriptor : AccessDescriptor)
    (hrange : descriptor.range = resolved.range) (hintent : descriptor.intent = .write) :
    (complete resolved descriptor hrange hintent).committed.written =
      some resolved.writeBytes := rfl

theorem complete_written_length (resolved : Resolved) (descriptor : AccessDescriptor)
    (hrange : descriptor.range = resolved.range) (_hintent : descriptor.intent = .write) :
    resolved.writeBytes.length = descriptor.range.size := by
  simp [Store32.Resolved.writeBytes, Store32.Resolved.range, hrange]

theorem truncate_written_prefix (resolved : Resolved) (descriptor : AccessDescriptor)
    (hrange : descriptor.range = resolved.range) (hintent : descriptor.intent = .write)
    (reads writes : Nat) :
    ((complete resolved descriptor hrange hintent).committed.truncate reads writes).written =
      some (resolved.writeBytes.take writes) := by
  rfl

end Grass.Assembly.Store32Execution
