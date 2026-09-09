import Grass.Platform.Win32.WriteFileHandoff
import Grass.Platform.Win32.CallEntry

/-!
# Actual CALL to checked WriteFile custody

This boundary retains the actual CALL result and repacks the original protocol
metadata against that result. It binds the saved slot and continuation to the
instruction receipt before issuing the full ABI batch. Import-symbol resolution
and native provider identity remain separate obligations.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86
open Grass.Platform.Win32.Loader

/-- Compatibility aliases for existing WriteFile consumers. -/
abbrev CallPolicy {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Execution.CallNormal before afterFetch afterRead afterStore displacement) :=
  CallEntry.CallPolicy loaded receipt

abbrev CallPolicy.ofFactory {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {policy : Execution.CpuAccessPolicy}
    (selected : Cpu.policy? loaded before = some policy)
    (success : Execution.CallFactory.Success policy before) :
    CallPolicy loaded success.receipt :=
  CallEntry.CallPolicy.ofFactory selected success

abbrev reachedCall? (before : ExecutionState.State ApiRequest)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement) :=
  CallEntry.reachedCall? before receipt

theorem reachedCall?_fields {before after : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    (success : reachedCall? before receipt = some after) :
    after.machine = receipt.result ∧ after.metadata = before.metadata ∧
      after.control = before.control :=
  CallEntry.reachedCall?_fields success

/-- One actual CALL, its exact reached carrier, and the full checked handoff.
This is a custody binding, not evidence that the selected target is a native
WriteFile export or that the provider has returned. -/
structure CallHandoff {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (before : ExecutionState.State ApiRequest)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement)
    (request : Request) (agent : ContextId) where
  policy : CallPolicy loaded receipt
  callerReady : before.ControlConsistent
  reached : ExecutionState.State ApiRequest
  reachedExact : reachedCall? before receipt = some reached
  abi : Abi.StackPlan reached.machine request
  continuation : abi.continuation = receipt.fetch.site.fallthroughRip
  returnProvenance : abi.returnSlot.provenance = receipt.storeDescriptor.provenance
  returnRange : abi.returnSlot.range = receipt.storeDescriptor.range
  handoff : EntryHandoff reached request abi agent
  caller : handoff.caller = inputs.thread

end Grass.Platform.Win32.WriteFile
