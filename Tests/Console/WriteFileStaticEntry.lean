import Grass.Refinement.Console.WriteFileStaticEntry
import Tests.Console.WriteFileCountEntry
import Tests.Assembly.StaticSection

/-! A real CALL consumes a suffix of an actual loaded static object. The source
selection shares that static symbol/image binding; this fixture does not claim
that its complete source code was emitted into the CALL-only text section. -/

namespace Grass.Tests.Console.WriteFileStaticEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Semantics
open Grass.Artifact.PE Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader Grass.Platform.Win32.WriteFile
open Grass.Refinement.Console

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def statics := Grass.Tests.Assembly.StaticSection.layout.get (by decide)
def description : ExecutableImageDescription :=
  { Grass.Tests.Win32WriteFileStackPlan.callDescription with
    sections := .fromList [
      { name := _root_.Tests.Artifact.PE.ImageWriter.textName
        contents := .fromList [0xff, 0x15, 0x22, 0x20, 0, 0]
        characteristics := 0x60000020 }, statics.rawSection] }
def plan := (prepareImage description).toOption.get (by decide)
def image : ImageInput := ⟨plan, (writeImage plan).toHostBytes, rfl⟩
def objectBinding := (SourceStaticBindings.resolveOne? plan statics 1 "second").get (by decide)
def cut : OutputCut objectBinding.object.declaration.bytes := ⟨1, by decide⟩

theorem actual_iat : plan.layout.importAddressRva? 0 0 = some 0x3028 := by decide

def symbols (delta : Nat) := SourceResolve.Symbols.checked
  [{ objectBinding.sourceSymbol with address := objectBinding.sourceSymbol.address + delta }]
  [{ name := "__imp_WriteFile", iatAddress := 0x3028 }] (by simp) (by simp)
def source := (SourceResolve.resolve? Grass.Tests.Console.WriteFileCountEntry.source.2.splice
  (symbols 0) 0x1000).get (by decide +kernel)
def selectedLocal := (Grass.Tests.Console.WriteFileCountEntry.selectLoad? source).get (by decide +kernel)

def inputs : EntryInputs :=
  { Grass.Tests.Win32WriteFileStackPlan.inputs with
    identities := (Grass.Tests.Win32LoaderEntry.inputsFor plan
      Grass.Tests.Win32WriteFileStackPlan.inputs.targets).identities
    gpr := fun register =>
      if register = .rdx then preferredBase image + BitVec.ofNat 64 (objectBinding.span.rva + cut.offset)
      else if register = .r8 then BitVec.ofNat 64 cut.remaining.length
      else if register = .r9 then
        Grass.Tests.Win32WriteFileStackPlan.inputs.gpr .rsp +
          BitVec.ofNat 64 selectedLocal.result.address.displacement
      else Grass.Tests.Win32WriteFileStackPlan.inputs.gpr register }
def loaded := (initialize? image inputs).get (by decide +kernel)
def incoming := loaded.initialState
def cpu := (Cpu.policy? loaded incoming).get (by decide +kernel)
def called := (CallFactory.call cpu incoming).toOption.get (by decide +kernel)
def protocol : CallProtocol.State ApiRequest :=
  CallProtocol.initial incoming.machine FreshSupply.initial (by decide +kernel)
def before : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol protocol incoming rfl (.caller inputs.thread)
theorem ready : before.ControlConsistent := by
  refine ⟨protocol, ExecutionState.State.ofCallProtocol_callProtocol? _ _ _ _, ⟨.thread, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel
def binding : CallPolicy loaded called.receipt := CallPolicy.ofFactory (by rfl) called
def evaluated : Raw.EvaluatedCall loaded before called.receipt :=
  { policy := cpu, selected := by rfl, flags := incoming.statusFlags
    success := called, evaluated := by rfl, receiptExact := HEq.rfl }

def prepared := WriteFileStaticEntry.prepare? objectBinding before called.receipt binding ready evaluated
  selectedLocal cut Grass.Tests.Win32WriteFileStackPlan.fifthArgument inputs.independentContext

/-- The result includes the actual call handoff, not only prepared arguments. -/
theorem actual_call_handoff : prepared.isSome := by decide +kernel
def result := prepared.get (by decide +kernel)
theorem actual_suffix : result.2.val.handoff.record.request.bytes = .fromList [5] := by decide +kernel
theorem nonzero_object_and_cut : objectBinding.object.offset = 8 ∧ cut.offset = 1 := by decide +kernel
theorem current_input : InputMatches called.result.machine.memory result.2.val.handoff.record.request :=
  WriteFileStaticArgument.requestOf_input called.result result.1
    (WriteFileCountArgument.argument binding.policy called.receipt selectedLocal)

def wrongSource := (SourceResolve.resolve? Grass.Tests.Console.WriteFileCountEntry.source.2.splice
  (symbols 1) 0x1000).get (by decide +kernel)
def wrongLocal := (Grass.Tests.Console.WriteFileCountEntry.selectLoad? wrongSource).get (by decide +kernel)

/-- Matching count layout cannot hide a different source static-symbol address. -/
theorem unrelated_static_symbol_refuses :
    (WriteFileStaticEntry.prepare? objectBinding before called.receipt binding ready evaluated
      wrongLocal cut Grass.Tests.Win32WriteFileStackPlan.fifthArgument inputs.independentContext).isNone := by
  decide +kernel

end Grass.Tests.Console.WriteFileStaticEntry
