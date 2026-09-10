import Grass.Refinement.Console.WriteFileResume

namespace Grass.Tests.Console.WriteFileResume

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState
open Grass.Refinement.Console.WriteFileResume

/-- A candidate cannot repair a changed nonvolatile cursor by assigning the
saved value. It must observe preservation in the actual provider state. -/
example {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {callBefore : ExecutionState.State ApiRequest}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {call : CallNormal callBefore.machine afterFetch afterTarget afterCall displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded callBefore call request provider)
    {before : RawState} {runtime : WriteFileRuntime}
    (resume : ProviderResume.Success loaded before entered.handoff.call (.writeFile runtime)
      entered.runtime.toReturnFrame call)
    (corrupted : before.machine.gpr .r13 ≠ callBefore.machine.gpr .r13) : False := by
  have retained := resume_nonvolatile entered resume ⟨.r13, by decide⟩
  rw [resume.gpr_other .r13 (by decide)] at retained
  exact corrupted retained

/-- Loan settlement may change the full memory state. The checked slot read
preserves the settled state, rather than reviving the old pending-loan state. -/
example {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32}
    {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    {before : RawState} {after : ProtocolState} {callId : CallProtocol.CallId}
    {runtime : CallRuntime} {frame : ReturnFrame}
    (resume : ProviderResume.Success loaded (afterReturn before after) callId runtime frame call)
    (settlementChanged : after.machine.memory ≠ before.machine.machine.memory) :
    resume.after.machine.machine.memory ≠ before.machine.machine.memory := by
  rw [resume_memory resume]
  exact settlementChanged

end Grass.Tests.Console.WriteFileResume
