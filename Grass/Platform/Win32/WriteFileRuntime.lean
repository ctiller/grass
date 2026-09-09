import Grass.Platform.Win32.WriteFileCall
import Grass.Platform.Win32.RawState

/-!
# Runtime state for an actual pending `WriteFile` call

This module computes the per-call runtime record from a reached ABI binding and
places it in an explicitly supplied prior runtime table.  It records no return
execution or provider activity.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
open Grass.Platform.Win32.Loader

/-- The immutable runtime coordinates for the actual reached ABI entry. -/
def CallHandoff.runtime {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) : WriteFileRuntime where
  entryRsp := handoff.reached.machine.gpr .rsp
  continuation := handoff.abi.continuation
  returnSlot := handoff.abi.returnSlot
  homeSlot := handoff.abi.homeSlot
  saved := captureNonvolatile before.machine.gpr
  fifthSlot := handoff.abi.entry.overlappedSlot
  accepted := 0

/-- The raw post-handoff carrier retains the actual checked handoff output and
updates the caller-supplied prior table at exactly its new call identity. -/
def CallHandoff.rawAfter {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable) :
    ExecutionState.RawState :=
  handoff.handoff.after.raw (prior.insert handoff.handoff.call (.writeFile handoff.runtime))

@[simp] theorem CallHandoff.runtime_loanPlan {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) :
    handoff.runtime.loanPlan = handoff.abi.loanPlan := rfl

@[simp] theorem CallHandoff.runtime_accepted {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) : handoff.runtime.accepted = 0 := rfl

@[simp] theorem CallHandoff.runtime_entryRsp {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) :
    handoff.runtime.entryRsp = handoff.reached.machine.gpr .rsp := rfl

@[simp] theorem CallHandoff.runtime_continuation {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) :
    handoff.runtime.continuation = handoff.abi.continuation := rfl

@[simp] theorem CallHandoff.runtime_returnSlot {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) :
    handoff.runtime.returnSlot = handoff.abi.returnSlot := rfl

@[simp] theorem CallHandoff.runtime_homeSlot {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) :
    handoff.runtime.homeSlot = handoff.abi.homeSlot := rfl

@[simp] theorem CallHandoff.runtime_fifthSlot {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) :
    handoff.runtime.fifthSlot = handoff.abi.entry.overlappedSlot := rfl

@[simp] theorem CallHandoff.runtime_saved {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) :
    handoff.runtime.saved = captureNonvolatile before.machine.gpr := rfl

/-- The saved callee-entry RSP restores exactly the pre-CALL RSP.  The retained
natural stack bound witnesses that the subtraction did not wrap. -/
theorem CallHandoff.runtime_restoredRsp {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) :
    handoff.runtime.restoredRsp = before.machine.gpr .rsp := by
  have reached := reachedCall?_fields handoff.reachedExact
  have noWrap : (before.machine.gpr .rsp - 8).toNat = (before.machine.gpr .rsp).toNat - 8 :=
    BitVec.toNat_sub_of_le receipt.stackNoUnderflow
  change handoff.reached.machine.gpr .rsp + BitVec.ofNat 64 8 = before.machine.gpr .rsp
  calc
    handoff.reached.machine.gpr .rsp + BitVec.ofNat 64 8 =
        receipt.result.gpr .rsp + BitVec.ofNat 64 8 := by rw [reached.1]
    _ = before.machine.gpr .rsp := by
      rw [receipt.rsp_exact]
      apply BitVec.eq_of_toNat_eq
      have eight : (BitVec.ofNat 64 8).toNat = 8 := by decide
      have sumLt : (before.machine.gpr .rsp - 8).toNat +
          (BitVec.ofNat 64 8).toNat < 2 ^ 64 := by
        rw [noWrap, eight]
        have bound := receipt.stackNoUnderflow
        have limit := (before.machine.gpr .rsp).isLt
        omega
      rw [BitVec.toNat_add_of_lt sumLt, noWrap, eight]
      have bound := receipt.stackNoUnderflow
      omega

@[simp] theorem CallHandoff.rawAfter_lookup {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable) :
    (handoff.rawAfter prior).calls.lookup handoff.handoff.call = some (.writeFile handoff.runtime) :=
  ExecutionState.RawState.setCall_lookup (handoff.handoff.after.raw prior)
    handoff.handoff.call (.writeFile handoff.runtime)

theorem CallHandoff.rawAfter_other {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable)
    {other : CallProtocol.CallId} (different : other ≠ handoff.handoff.call) :
    (handoff.rawAfter prior).calls.lookup other = prior.lookup other :=
  ExecutionState.RawState.setCall_other (handoff.handoff.after.raw prior) different
    (.writeFile handoff.runtime)

@[simp] theorem CallHandoff.rawAfter_checked? {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable) :
    (handoff.rawAfter prior).checked? = some handoff.handoff.after :=
  ExecutionState.State.raw_checked? handoff.handoff.after _

@[simp] theorem CallHandoff.rawAfter_machine {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable) :
    (handoff.rawAfter prior).machine = handoff.handoff.after.machine := rfl

@[simp] theorem CallHandoff.rawAfter_metadata {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable) :
    (handoff.rawAfter prior).metadata = handoff.handoff.after.metadata := rfl

@[simp] theorem CallHandoff.rawAfter_control {image : ImageInput} {inputs : EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable) :
    (handoff.rawAfter prior).control = handoff.handoff.after.control := rfl

end Grass.Platform.Win32.WriteFile
