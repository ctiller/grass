import Grass.ISA.X86.Execution.AccessFree
import Grass.ISA.X86.Execution.CompletionFlags

/-!
# Normal register MOV completion

The admitted slice is the production register/register MOV at 32 or 64 bits,
and the production `B8+rd` register-immediate form at 32 bits.  Construction is
conditional on an actual fetch and an actual access-free normal operation run.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

/-- Full flags after ordinary completed MOV: status and other retained bits are
preserved, while RF is cleared by the common completed-instruction rule. -/
def completedMoveRflags (state : State) : BitVec 64 := completedPushRflags state

theorem completedMoveRflags_status (state : State) :
    RegisterSemantics.Flags.fromBits (completedMoveRflags state) = state.statusFlags :=
  completedPushRflags_status state

theorem completedMoveRflags_resume (state : State) :
    (completedMoveRflags state).getLsbD 16 = false :=
  completedPushRflags_resume state

/-- The bounded production MOV forms admitted by this execution adapter. -/
inductive MoveInstruction where
  | regReg (width : BasicInstructions.Width) (destination source : Gpr)
  | imm32 (destination : Gpr) (value : BitVec 32)
deriving DecidableEq, Repr

namespace MoveInstruction

def encoding : MoveInstruction → InsnEncoding
  | .regReg width destination source => BasicInstructions.movRegReg width destination source
  | .imm32 destination value => movRegImm32 destination value

def destination : MoveInstruction → Gpr
  | .regReg _ destination _ => destination
  | .imm32 destination _ => destination

def effect (instruction : MoveInstruction) (state : State) : RegisterSemantics.Effect :=
  match instruction with
  | .regReg width destination source =>
      RegisterSemantics.evaluate .mov width (state.gpr destination) (state.gpr source)
        state.statusFlags
  | .imm32 destination value =>
      RegisterSemantics.evaluate .mov .w32 (state.gpr destination) (BitVec.setWidth 64 value)
        state.statusFlags

end MoveInstruction

/-- An actual fetched production MOV and its access-free normal completion. -/
structure MoveNormal (before : State) (afterFetch afterCompute : MachineState)
    (instruction : MoveInstruction) where
  execution : AccessFree before afterFetch afterCompute
  encoding : execution.fetch.site.encoding = instruction.encoding

namespace MoveNormal

def result {before : State} {afterFetch afterCompute : MachineState}
    {instruction : MoveInstruction}
    (receipt : MoveNormal before afterFetch afterCompute instruction) : State :=
  { before.withGpr instruction.destination
      ((instruction.effect before).destination (before.gpr instruction.destination)) with
    machine := afterCompute
    rip := receipt.execution.fetch.site.fallthroughRip
    rflags := completedMoveRflags before }

theorem destination_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : MoveInstruction}
    (receipt : MoveNormal before afterFetch afterCompute instruction) :
    receipt.result.gpr instruction.destination =
      (instruction.effect before).destination (before.gpr instruction.destination) := by
  simp [result]

theorem gpr_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : MoveInstruction}
    (receipt : MoveNormal before afterFetch afterCompute instruction) (register : Gpr)
    (other : register ≠ instruction.destination) :
    receipt.result.gpr register = before.gpr register := by
  simp [result, State.withGpr, other]

theorem rip_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : MoveInstruction}
    (receipt : MoveNormal before afterFetch afterCompute instruction) :
    receipt.result.rip = receipt.execution.fetch.site.fallthroughRip := rfl

theorem rflags_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : MoveInstruction}
    (receipt : MoveNormal before afterFetch afterCompute instruction) :
    receipt.result.rflags = completedMoveRflags before := rfl

theorem state_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : MoveInstruction}
    (receipt : MoveNormal before afterFetch afterCompute instruction) :
    receipt.result.machine.memory = before.machine.memory ∧
      receipt.result.machine.obligations = before.machine.obligations :=
  receipt.execution.state_frame

theorem storage_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : MoveInstruction}
    (receipt : MoveNormal before afterFetch afterCompute instruction) :
    receipt.result.machine.memory.allocations = before.machine.memory.allocations ∧
      receipt.result.machine.memory.backings = before.machine.memory.backings :=
  receipt.execution.storage_frame

theorem events_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : MoveInstruction}
    (receipt : MoveNormal before afterFetch afterCompute instruction) :
    ∃ valid, receipt.result.machine.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some instruction.encoding.toBytes := by
  obtain ⟨valid, appended, bytes, _⟩ := receipt.execution.fetched_event
  exact ⟨valid, appended, by simpa [receipt.encoding] using bytes⟩

theorem regReg_w32_high_clear {before : State} {afterFetch afterCompute : MachineState}
    {destination source : Gpr}
    (receipt : MoveNormal before afterFetch afterCompute
      (.regReg .w32 destination source)) :
    BitVec.extractLsb' 32 32 (receipt.result.gpr destination) = 0 := by
  have destinationExact := receipt.destination_exact
  simp only [MoveInstruction.destination] at destinationExact
  rw [destinationExact]
  apply RegisterSemantics.w32_write_clears_high .mov
    (before.gpr destination) (before.gpr source) _ before.statusFlags
  rfl

theorem imm32_high_clear {before : State} {afterFetch afterCompute : MachineState}
    {destination : Gpr} {value : BitVec 32}
    (receipt : MoveNormal before afterFetch afterCompute (.imm32 destination value)) :
    BitVec.extractLsb' 32 32 (receipt.result.gpr destination) = 0 := by
  have destinationExact := receipt.destination_exact
  simp only [MoveInstruction.destination] at destinationExact
  rw [destinationExact]
  apply RegisterSemantics.w32_write_clears_high .mov
    (before.gpr destination) (BitVec.setWidth 64 value) _ before.statusFlags
  rfl

end MoveNormal
end Grass.ISA.X86.Execution
