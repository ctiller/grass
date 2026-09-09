import Grass.ISA.X86.Execution.AccessFree
import Grass.ISA.X86.Execution.CompletionFlags
import Grass.ISA.X86.RegisterDecode

/-!
# Normal register arithmetic completion

This bounded adapter covers the production register-direct ADD, SUB, CMP,
TEST, and XOR encodings at 32 and 64 bits, plus signed CMP immediate. Undefined
status flags remain relational through `Flags.Allows`; the adapter never picks
a representative value for them.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

inductive ArithmeticInstruction where
  | add (width : BasicInstructions.Width) (destination source : Gpr)
  | sub (width : BasicInstructions.Width) (destination source : Gpr)
  | cmp (width : BasicInstructions.Width) (destination source : Gpr)
  | test (width : BasicInstructions.Width) (destination source : Gpr)
  | xor (width : BasicInstructions.Width) (destination source : Gpr)
  | cmpImmediate (width : BasicInstructions.Width) (destination : Gpr)
      (immediate : ImmediateArithmetic.Immediate)
deriving DecidableEq, Repr

namespace ArithmeticInstruction

def encoding : ArithmeticInstruction → InsnEncoding
  | .add width destination source => BasicInstructions.addRegReg width destination source
  | .sub width destination source => BasicInstructions.subRegReg width destination source
  | .cmp width destination source => BasicInstructions.cmpRegReg width destination source
  | .test width destination source => BasicInstructions.testRegReg width destination source
  | .xor width destination source => BasicInstructions.xorRegReg width destination source
  | .cmpImmediate width destination immediate =>
      ImmediateArithmetic.encode .cmp width destination immediate

structure Selection (encoding : InsnEncoding) where
  instruction : ArithmeticInstruction
  encoding_eq : instruction.encoding = encoding

def destination : ArithmeticInstruction → Gpr
  | .add _ destination _ | .sub _ destination _ | .cmp _ destination _
  | .test _ destination _ | .xor _ destination _
  | .cmpImmediate _ destination _ => destination

def effect (instruction : ArithmeticInstruction) (state : State) : RegisterSemantics.Effect :=
  match instruction with
  | .add width destination source => RegisterSemantics.evaluate .add width
      (state.gpr destination) (state.gpr source) state.statusFlags
  | .sub width destination source => RegisterSemantics.evaluate .sub width
      (state.gpr destination) (state.gpr source) state.statusFlags
  | .cmp width destination source => RegisterSemantics.evaluate .cmp width
      (state.gpr destination) (state.gpr source) state.statusFlags
  | .test width destination source => RegisterSemantics.evaluate .test width
      (state.gpr destination) (state.gpr source) state.statusFlags
  | .xor width destination source => RegisterSemantics.evaluate .xor width
      (state.gpr destination) (state.gpr source) state.statusFlags
  | .cmpImmediate width destination immediate => RegisterSemantics.evaluateImmediate .cmp width
      (state.gpr destination) immediate state.statusFlags

private def ofRegisterSelection {encoding : InsnEncoding}
    (selected : RegisterDecode.Selection encoding) : Option (Selection encoding) :=
  let source := selected.instruction.source
  let destination := selected.instruction.destination
  let width := selected.instruction.width
  let candidate : Option ArithmeticInstruction :=
    match selected.instruction.kind with
    | .add => some (.add width destination source)
    | .sub => some (.sub width destination source)
    | .cmp => some (.cmp width destination source)
    | .test => some (.test width destination source)
    | .xor => some (.xor width destination source)
    | .mov => none
  match candidate with
  | none => none
  | some instruction =>
      if h : instruction.encoding = encoding then some ⟨instruction, h⟩ else none

private def selectImmediate (encoding : InsnEncoding) : Option (Selection encoding) := do
  let operands ← RegisterDecode.reconstruct encoding
  let immediate ← match encoding.imm with
    | .i8 bits => some (ImmediateArithmetic.Immediate.i8 bits)
    | .i32 bits => some (ImmediateArithmetic.Immediate.i32 bits)
    | _ => none
  let instruction := .cmpImmediate operands.width operands.destination immediate
  if h : instruction.encoding = encoding then some ⟨instruction, h⟩ else none

/-- Select the bounded arithmetic family by equality with production encoders. -/
def select (encoding : InsnEncoding) : Option (Selection encoding) :=
  match RegisterDecode.select encoding with
  | some selected => ofRegisterSelection selected
  | none => selectImmediate encoding

end ArithmeticInstruction

structure ArithmeticNormal (before : State) (afterFetch afterCompute : MachineState)
    (instruction : ArithmeticInstruction) where
  execution : AccessFree before afterFetch afterCompute
  encoding : execution.fetch.site.encoding = instruction.encoding
  /-- The full post-instruction flags image; undefined modeled bits remain choices. -/
  afterRflags : BitVec 64
  flagsAllowed : (instruction.effect before).flags.Allows
    (RegisterSemantics.Flags.fromBits afterRflags)
  /-- Bits outside the modeled status flags are framed, except that RF is cleared. -/
  outsideStatusFrame : afterRflags &&& ~~~statusMask =
    (before.rflags &&& ~~~statusMask) &&& ~~~resumeMask
  resumeCleared : afterRflags.getLsbD 16 = false

namespace ArithmeticNormal

def result {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) : State :=
  { before.withGpr instruction.destination
      ((instruction.effect before).destination (before.gpr instruction.destination)) with
    machine := afterCompute
    rip := receipt.execution.fetch.site.fallthroughRip
    rflags := receipt.afterRflags }

theorem destination_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) :
    receipt.result.gpr instruction.destination =
      (instruction.effect before).destination (before.gpr instruction.destination) := by
  simp [result]

theorem gpr_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) (register : Gpr)
    (other : register ≠ instruction.destination) :
    receipt.result.gpr register = before.gpr register := by
  simp [result, State.withGpr, other]

theorem rip_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) :
    receipt.result.rip = receipt.execution.fetch.site.fallthroughRip := rfl

theorem flags_conform {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) :
    (instruction.effect before).flags.Allows receipt.result.statusFlags :=
  receipt.flagsAllowed

theorem rflags_outside_status {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) :
    receipt.result.rflags &&& ~~~statusMask =
      (before.rflags &&& ~~~statusMask) &&& ~~~resumeMask :=
  receipt.outsideStatusFrame

theorem rflags_resume_cleared {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) :
    receipt.result.rflags.getLsbD 16 = false := receipt.resumeCleared

theorem state_frame {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) :
    receipt.result.machine.memory = before.machine.memory ∧
      receipt.result.machine.obligations = before.machine.obligations :=
  receipt.execution.state_frame

theorem events_exact {before : State} {afterFetch afterCompute : MachineState}
    {instruction : ArithmeticInstruction}
    (receipt : ArithmeticNormal before afterFetch afterCompute instruction) :
    ∃ valid, receipt.result.machine.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some instruction.encoding.toBytes := by
  obtain ⟨valid, appended, bytes, _⟩ := receipt.execution.fetched_event
  exact ⟨valid, appended, by simpa [receipt.encoding] using bytes⟩

end ArithmeticNormal

end Grass.ISA.X86.Execution
