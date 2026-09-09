import Grass.ISA.X86.Execution.AccessFree
import Grass.ISA.X86.Execution.CompletionFlags

/-! Bounded normal completion for the two 64-bit LEA addressing forms emitted by Hello. -/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

inductive LeaBase where
  | ripRelative
  | rsp
deriving DecidableEq, Repr

structure LeaInstruction where
  base : LeaBase
  destination : Gpr
  displacement : BitVec 32
deriving DecidableEq, Repr

namespace LeaInstruction

def operand (instruction : LeaInstruction) : MemOperand :=
  match instruction.base with
  | .ripRelative => .ripRelative instruction.displacement
  | .rsp => .base .rsp instruction.displacement

def encoding? (instruction : LeaInstruction) : Option InsnEncoding :=
  leaR64 instruction.destination instruction.operand

/-- Recover only the RIP-relative and RSP+disp32 LEA forms from the encoding's
existing register and addressing fields, then validate the complete encoding. -/
private def accept (encoding : InsnEncoding) (instruction : LeaInstruction) :
    Option LeaInstruction :=
  if instruction.encoding? = some encoding then some instruction else none

def select (encoding : InsnEncoding) : Option LeaInstruction :=
  match encoding.modrm with
  | none => none
  | some modrm =>
      let rexR := encoding.rex.map (·.r) |>.getD 0
      let rexX := encoding.rex.map (·.x) |>.getD 0
      let rexB := encoding.rex.map (·.b) |>.getD 0
      let destination := Gpr.ofBits rexR modrm.reg
      match decodeMem
          { mod := modrm.mod, rm := modrm.rm, sib := encoding.sib, disp := encoding.disp,
            rexX := rexX, rexB := rexB } with
      | some (.ripRelative displacement) =>
          accept encoding ⟨.ripRelative, destination, displacement⟩
      | some (.base .rsp displacement) => accept encoding ⟨.rsp, destination, displacement⟩
      | _ => none

theorem select_sound {encoding : InsnEncoding} {instruction : LeaInstruction}
    (selected : select encoding = some instruction) :
    instruction.encoding? = some encoding := by
  unfold select at selected
  split at selected <;> try contradiction
  dsimp at selected
  split at selected <;> try contradiction
  all_goals unfold accept at selected; split at selected <;> simp_all

def baseValue (instruction : LeaInstruction) (before : State)
    (fallthrough : BitVec 64) : BitVec 64 :=
  match instruction.base with
  | .ripRelative => fallthrough
  | .rsp => before.gpr .rsp

def effectiveAddress (instruction : LeaInstruction) (before : State)
    (fallthrough : BitVec 64) : BitVec 64 :=
  instruction.baseValue before fallthrough + BitVec.ofInt 64 instruction.displacement.toInt

end LeaInstruction

structure LeaNormal (before : State) (afterFetch afterCompute : MachineState)
    (instruction : LeaInstruction) where
  execution : AccessFree before afterFetch afterCompute
  encoding : instruction.encoding? = some execution.fetch.site.encoding

namespace LeaNormal

def result {before : State} {afterFetch afterCompute : MachineState}
    {instruction : LeaInstruction}
    (receipt : LeaNormal before afterFetch afterCompute instruction) : State :=
  { before.withGpr instruction.destination
      (instruction.effectiveAddress before receipt.execution.fetch.site.fallthroughRip) with
    machine := afterCompute
    rip := receipt.execution.fetch.site.fallthroughRip
    rflags := completedPushRflags before }

theorem destination_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : LeaInstruction} (receipt : LeaNormal before afterFetch afterCompute instruction) :
    receipt.result.gpr instruction.destination =
      instruction.effectiveAddress before receipt.execution.fetch.site.fallthroughRip := by
  simp [result]

theorem gpr_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : LeaInstruction} (receipt : LeaNormal before afterFetch afterCompute instruction)
    (register : Gpr) (other : register ≠ instruction.destination) :
    receipt.result.gpr register = before.gpr register := by
  simp [result, State.withGpr, other]

theorem rip_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : LeaInstruction} (receipt : LeaNormal before afterFetch afterCompute instruction) :
    receipt.result.rip = receipt.execution.fetch.site.fallthroughRip := rfl

theorem rflags_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : LeaInstruction} (receipt : LeaNormal before afterFetch afterCompute instruction) :
    receipt.result.rflags = completedPushRflags before := rfl

theorem state_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : LeaInstruction} (receipt : LeaNormal before afterFetch afterCompute instruction) :
    receipt.result.machine.memory = before.machine.memory ∧
      receipt.result.machine.obligations = before.machine.obligations :=
  receipt.execution.state_frame

theorem storage_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : LeaInstruction} (receipt : LeaNormal before afterFetch afterCompute instruction) :
    receipt.result.machine.memory.allocations = before.machine.memory.allocations ∧
      receipt.result.machine.memory.backings = before.machine.memory.backings :=
  receipt.execution.storage_frame

theorem events_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : LeaInstruction} (receipt : LeaNormal before afterFetch afterCompute instruction) :
    ∃ valid, receipt.result.machine.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some receipt.execution.fetch.site.encoding.toBytes :=
by
  obtain ⟨valid, appended, bytes, _⟩ := receipt.execution.fetched_event
  exact ⟨valid, appended, bytes⟩

theorem ripRelative_address {before : State} {afterFetch afterCompute : MachineState}
    {destination : Gpr} {displacement : BitVec 32}
    (receipt : LeaNormal before afterFetch afterCompute
      ⟨.ripRelative, destination, displacement⟩) :
    receipt.result.gpr destination = receipt.execution.fetch.site.fallthroughRip +
      BitVec.ofInt 64 displacement.toInt := receipt.destination_exact

theorem rsp_address {before : State} {afterFetch afterCompute : MachineState}
    {destination : Gpr} {displacement : BitVec 32}
    (receipt : LeaNormal before afterFetch afterCompute ⟨.rsp, destination, displacement⟩) :
    receipt.result.gpr destination = before.gpr .rsp + BitVec.ofInt 64 displacement.toInt :=
  receipt.destination_exact

end LeaNormal
end Grass.ISA.X86.Execution
