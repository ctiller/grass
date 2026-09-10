import Grass.Refinement.Console.WriteFileCountEntry
import Tests.Assembly.SourceResolve
import Tests.Assembly.FrameLea
import Tests.Platform.Win32WriteFileStackPlan

namespace Grass.Tests.Console.WriteFileCountEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Refinement.Console

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def sourceFor (text : List Char) : Option (Σ frame : SourceFrame.Result, SourceResolve.Result frame 0) := do
  let body ← (SourceInput.extractHelloSourceChars text).toOption
  let frame ← SourceFrame.derive? body
  let splice ← SourceSplice.derive? frame 0
  let symbols ← Grass.Tests.Assembly.SourceResolve.checkedSymbols
  let source ← SourceResolve.resolve? splice symbols 1000
  pure ⟨frame, source⟩

def selectLoad? {frame : SourceFrame.Result} (source : SourceResolve.Result frame 0) :
    Option (SourceResolve.LoadSelection source) :=
  let index := source.splice.source.outputs.findIdx fun output =>
    match output with | .load .. => true | _ => false
  match found : source.splice.source.outputs[index]? with
  | some (.load _ _ _) => some (source.loadSelectionOfSourceAt found)
  | _ => none

/-- The source fixture and actual machine execution contain no count-address LEA. -/
def withoutLea := Grass.Tests.Assembly.FrameLea.sample
  (source_chars "withStack (transferred : UInt32 := 0)")
  (source_chars "call qword ptr [rip + __imp_WriteFile]\nmov eax, transferred")
def source := (sourceFor withoutLea).get (by decide +kernel)
def selectedLocal := (selectLoad? source.2).get (by decide +kernel)

open Grass.Tests.Win32WriteFileStackPlan in
def incoming : State :=
  { initial with gpr := fun register => if register = .r9 then
      initial.gpr .r9 - BitVec.ofNat 64 request.countSlot.range.start +
        BitVec.ofNat 64 selectedLocal.result.address.range.start
    else initial.gpr register }

abbrev loaded := Grass.Tests.Win32WriteFileStackPlan.loaded
abbrev inputs := Grass.Tests.Win32WriteFileStackPlan.inputs
def cpu := (Cpu.policy? loaded incoming).get (by decide +kernel)
def called := (CallFactory.call cpu incoming).toOption.get (by decide +kernel)
def protocol : CallProtocol.State ApiRequest :=
  CallProtocol.initial incoming.machine FreshSupply.initial (by decide +kernel)
def before : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol protocol incoming rfl (.caller inputs.thread)
theorem ready : before.ControlConsistent := by
  refine ⟨protocol, ExecutionState.State.ofCallProtocol_callProtocol? _ _ _ _, ⟨.thread, ?_⟩, ?_⟩
  · decide
  · decide
def binding : CallPolicy loaded called.receipt := CallPolicy.ofFactory (by rfl) called
def evaluated : Raw.EvaluatedCall loaded before called.receipt :=
  { policy := cpu, selected := by rfl, flags := incoming.statusFlags
    success := called, evaluated := by rfl, receiptExact := HEq.rfl }

open Grass.Tests.Win32WriteFileStackPlan in
def prepared := WriteFileCountEntry.prepareCountCall? before called.receipt binding ready evaluated
  selectedLocal request.buffer request.bytes fifthArgument inputs.independentContext

/-- Already-correct R9 satisfies the same checked entry contract without LEA. -/
theorem preexisting_r9_accepts : prepared.isSome := by decide +kernel

def handoff := prepared.get (by decide +kernel)
theorem canonical_count_retained : handoff.handoff.record.request.countSlot =
    WriteFileCountArgument.argument binding.policy selectedLocal := rfl

/-- The source-specific producer rejects a different named local even when its
layout gives the same numeric address and width. -/
def otherText := Grass.Tests.Assembly.FrameLea.sample
  (source_chars "withStack (other : UInt32 := 0)")
  (source_chars "call qword ptr [rip + __imp_WriteFile]\nmov eax, other")
def otherSource := (sourceFor otherText).get (by decide +kernel)
def otherLocal := (selectLoad? otherSource.2).get (by decide +kernel)
theorem other_local_same_range : otherLocal.result.address.range = selectedLocal.result.address.range := by decide +kernel

open Grass.Tests.Win32WriteFileStackPlan in
theorem other_local_refuses :
    (WriteFileCountEntry.prepareCountCall? before called.receipt binding ready evaluated
      otherLocal request.buffer request.bytes fifthArgument inputs.independentContext).isNone := by decide +kernel

/-- Moving the named local in its source frame changes the canonical address;
the unchanged incoming R9 is then rejected. -/
def shiftedText := Grass.Tests.Assembly.FrameLea.sample
  (source_chars "withStack (padding : UInt32 := 0) withStack (transferred : UInt32 := 0)")
  (source_chars "call qword ptr [rip + __imp_WriteFile]\nmov eax, transferred")
def shiftedSource := (sourceFor shiftedText).get (by decide +kernel)
def shiftedLocal := (selectLoad? shiftedSource.2).get (by decide +kernel)

open Grass.Tests.Win32WriteFileStackPlan in
theorem changed_frame_address_refuses :
    (WriteFileCountEntry.prepareCountCall? before called.receipt binding ready evaluated
      shiftedLocal request.buffer request.bytes fifthArgument inputs.independentContext).isNone := by decide +kernel

def canonical := WriteFileCountArgument.argument binding.policy selectedLocal

open Grass.Tests.Win32WriteFileStackPlan in
theorem wrong_count_width_refuses :
    (WriteFileSourceEntry.prepareCall? before called.receipt binding ready request.buffer
      { canonical with range := { canonical.range with size := 8 } } request.bytes fifthArgument
      inputs.independentContext).isNone := by decide +kernel

open Grass.Tests.Win32WriteFileStackPlan in
theorem wrong_count_space_refuses :
    (WriteFileSourceEntry.prepareCall? before called.receipt binding ready request.buffer
      { canonical with provenance := { canonical.provenance with space := .cpuPhysical } }
      request.bytes fifthArgument inputs.independentContext).isNone := by decide +kernel

end Grass.Tests.Console.WriteFileCountEntry
