import Grass.ISA.X86.Execution.AccessFree
import Grass.ISA.X86.Execution.CompletionFlags
import Grass.ISA.X86.Rel32

/-!
# Normal rel32 branch completion

This adapter covers production rel32 JMP, JZ/JE, and JA encodings. The signed
displacement is relative to the actual fetched site's fallthrough address.
`BranchNormal.targetFits` applies only when the selected branch is taken.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

/-- Full flags after an ordinary completed branch. -/
def completedBranchRflags (state : State) : BitVec 64 := completedPushRflags state

inductive BranchInstruction where
  | jump (displacement : BitVec 32)
  | equal (displacement : BitVec 32)
  | above (displacement : BitVec 32)
deriving DecidableEq, Repr

namespace BranchInstruction

def kind : BranchInstruction → Rel32.Kind
  | .jump _ => .jump
  | .equal _ => .equal
  | .above _ => .above

def displacement : BranchInstruction → BitVec 32
  | .jump bits | .equal bits | .above bits => bits

def encoding (instruction : BranchInstruction) : InsnEncoding :=
  Rel32.encode instruction.kind instruction.displacement

structure Selection (encoding : InsnEncoding) where
  instruction : BranchInstruction
  encoding_eq : instruction.encoding = encoding

def taken (instruction : BranchInstruction) (flags : RegisterSemantics.Flags Bool) : Bool :=
  match instruction with
  | .jump _ => true
  | .equal _ => flags.zf
  | .above _ => !flags.cf && !flags.zf

private def tryInstruction (encoding : InsnEncoding) (instruction : BranchInstruction) :
    Option (Selection encoding) :=
  if h : instruction.encoding = encoding then some ⟨instruction, h⟩ else none

/-- Select JMP, JZ/JE, or JA by equality with the three production encoders. -/
def select (encoding : InsnEncoding) : Option (Selection encoding) :=
  match encoding.imm with
  | .i32 bits =>
      (tryInstruction encoding (.jump bits)).orElse fun _ =>
        (tryInstruction encoding (.equal bits)).orElse fun _ =>
          tryInstruction encoding (.above bits)
  | _ => none

end BranchInstruction

structure BranchNormal (before : State) (afterFetch afterCompute : MachineState)
    (instruction : BranchInstruction) where
  execution : AccessFree before afterFetch afterCompute
  encoding : execution.fetch.site.encoding = instruction.encoding
  /-- Only a selected target must be representable as a 64-bit linear address. -/
  targetFits : instruction.taken before.statusFlags = true →
    0 ≤ (Int.ofNat execution.fetch.site.fallthroughRip.toNat + instruction.displacement.toInt) ∧
      (Int.ofNat execution.fetch.site.fallthroughRip.toNat + instruction.displacement.toInt) <
        Int.ofNat (2 ^ 64)

namespace BranchNormal

def target {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction) : BitVec 64 :=
  BitVec.ofInt 64
    (Int.ofNat receipt.execution.fetch.site.fallthroughRip.toNat + instruction.displacement.toInt)

def result {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction) : State :=
  { before with
    machine := afterCompute
    rip := if instruction.taken before.statusFlags then receipt.target
      else receipt.execution.fetch.site.fallthroughRip
    rflags := completedBranchRflags before }

theorem taken_rip {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction)
    (taken : instruction.taken before.statusFlags = true) :
    receipt.result.rip = receipt.target := by simp [result, taken]

theorem not_taken_rip {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction)
    (notTaken : instruction.taken before.statusFlags = false) :
    receipt.result.rip = receipt.execution.fetch.site.fallthroughRip := by
  simp [result, notTaken]

theorem taken_target_fits {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction)
    (taken : instruction.taken before.statusFlags = true) :
    0 ≤ (Int.ofNat receipt.execution.fetch.site.fallthroughRip.toNat +
      instruction.displacement.toInt) ∧
      (Int.ofNat receipt.execution.fetch.site.fallthroughRip.toNat +
        instruction.displacement.toInt) < Int.ofNat (2 ^ 64) :=
  receipt.targetFits taken

theorem gpr_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction) :
    receipt.result.gpr = before.gpr := rfl

theorem rflags_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction) :
    receipt.result.rflags = completedBranchRflags before := rfl

theorem state_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction) :
    receipt.result.machine.memory = before.machine.memory ∧
      receipt.result.machine.obligations = before.machine.obligations :=
  receipt.execution.state_frame

theorem events_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction) :
    ∃ valid, receipt.result.machine.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some instruction.encoding.toBytes := by
  obtain ⟨valid, appended, bytes, _⟩ := receipt.execution.fetched_event
  exact ⟨valid, appended, by simpa [receipt.encoding] using bytes⟩

end BranchNormal
end Grass.ISA.X86.Execution
