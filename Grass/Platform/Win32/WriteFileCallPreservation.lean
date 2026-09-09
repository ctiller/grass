import Grass.Platform.Win32.WriteFilePreservation
import Grass.ISA.X86.Execution.CallNormal

/-!
# Preservation from an actual `CALL` return-address store

This joins an actual completed `CALL` store to the bounded `WriteFile` custody
history.  It does not interpret the later protocol return as an x86 `RET`.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86

namespace Abi

/-- The concrete return-address byte saved by an actual normal call.  The
initialized byte is obtained from `CallNormal.saved_cell`, never supplied as a
separate ABI observation. -/
theorem CallNormal.saved_return_cell {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (call : Execution.CallNormal before afterFetch afterRead afterStore displacement)
    {request : Request} (stack : StackPlan call.result request)
    (returnProvenance : stack.returnSlot.provenance = call.storeDescriptor.provenance)
    (returnRange : stack.returnSlot.range = call.storeDescriptor.range) (i : Fin 8) :
    call.result.machine.memory.cellAt? stack.returnSlot.provenance.root
      (stack.returnSlot.range.start + i.val) =
      ((Grass.ISA.X86.le64 call.fetch.site.fallthroughRip)[i.val]?).map (·, true) := by
  change afterStore.memory.cellAt? stack.returnSlot.provenance.root
    (stack.returnSlot.range.start + i.val) = _
  rw [returnProvenance, returnRange]
  have covered : call.storeDescriptor.range.Covers
      (call.storeDescriptor.range.start + i.val) := by
    unfold ByteRange.Covers ByteRange.stop
    rw [call.storeWidth]
    omega
  simpa using call.saved_cell (call.storeDescriptor.range.start + i.val) covered

/-- `CallNormal.saved_return_cell_preserved` proves preservation of each actual saved continuation byte.
The protocol state is explicitly tied to the post-`CALL` architectural machine. -/
theorem CallNormal.saved_return_cell_preserved {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (call : Execution.CallNormal before afterFetch afterRead afterStore displacement)
    {plan : LoanPlan} {realization : Realization} {initial : ProtocolState}
    {request : Request} {callId : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state callId record}
    (stack : StackPlan call.result request)
    (returnProvenance : stack.returnSlot.provenance = call.storeDescriptor.provenance)
    (returnRange : stack.returnSlot.range = call.storeDescriptor.range)
    (initialMachine : initial.machine = call.result.machine) (planExact : plan = stack.loanPlan)
    (requestExact : record.request = request)
    (history : History plan realization initial callId record frontier) (i : Fin 8) :
    state.machine.memory.cellAt? stack.returnSlot.provenance.root
      (stack.returnSlot.range.start + i.val) =
      ((Grass.ISA.X86.le64 call.fetch.site.fallthroughRip)[i.val]?).map (·, true) := by
  calc
    state.machine.memory.cellAt? stack.returnSlot.provenance.root
        (stack.returnSlot.range.start + i.val) =
        call.result.machine.memory.cellAt? stack.returnSlot.provenance.root
          (stack.returnSlot.range.start + i.val) :=
      stack.return_cellAt?_preserved initialMachine.symm planExact requestExact history i
    _ = _ := saved_return_cell call stack returnProvenance returnRange i

/-- `CallNormal.saved_return_cell_preserved_after_return` proves preservation of each actual saved continuation byte.
This theorem remains a custody result and does not claim that a physical return
instruction executed. -/
theorem CallNormal.saved_return_cell_preserved_after_return {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (call : Execution.CallNormal before afterFetch afterRead afterStore displacement)
    {plan : LoanPlan} {selected : ReturnInterpretation} {realization : Realization}
    {initial : ProtocolState} {request : Request} {callId : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {beforeState afterState : ProtocolState}
    {frontier : Prefix plan beforeState callId record} (stack : StackPlan call.result request)
    (returnProvenance : stack.returnSlot.provenance = call.storeDescriptor.provenance)
    (returnRange : stack.returnSlot.range = call.storeDescriptor.range)
    (initialMachine : initial.machine = call.result.machine) (planExact : plan = stack.loanPlan)
    (requestExact : record.request = request)
    (history : History plan realization initial callId record frontier) {result : ReturnResult}
    (returned : MatchedReturn selected history result afterState) (i : Fin 8) :
    afterState.machine.memory.cellAt? stack.returnSlot.provenance.root
      (stack.returnSlot.range.start + i.val) =
      ((Grass.ISA.X86.le64 call.fetch.site.fallthroughRip)[i.val]?).map (·, true) := by
  calc
    afterState.machine.memory.cellAt? stack.returnSlot.provenance.root
        (stack.returnSlot.range.start + i.val) =
        call.result.machine.memory.cellAt? stack.returnSlot.provenance.root
          (stack.returnSlot.range.start + i.val) :=
      stack.return_cellAt?_preserved_after_return initialMachine.symm planExact requestExact
        history returned i
    _ = _ := saved_return_cell call stack returnProvenance returnRange i

end Abi
end Grass.Platform.Win32.WriteFile
