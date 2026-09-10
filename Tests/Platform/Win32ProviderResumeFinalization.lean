import Grass.Platform.Win32.ProviderResumeFinalization
import Grass.Platform.Win32.GetStdHandleRuntime

/-! The second returning API consumes the shared laws without a Console import
or a WriteFile matched-history/result premise. These are conditional receipt
regressions, not an installed GetStdHandle provider transition. -/

namespace Grass.Tests.Win32ProviderResumeFinalization

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {original : ExecutionState.State ApiRequest}
  {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
  {call : CallNormal original.machine afterFetch afterTarget afterCall displacement}
  {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded original call agent)
  {before : RawState} {providerState settled : CallProtocol.State ApiRequest}

/-- GetStdHandle's heterogeneous pending record settles caller control through
the same implementation used by the WriteFile source consumer. -/
example
    (ran : CallProtocol.return? providerState entered.handoff.call
      entered.handoff.record.caller entered.handoff.record.agent entered.handoff.record.ids =
      some (entered.handoff.record, settled))
    (resume : ProviderResume.Success loaded (ProviderResume.afterReturn before settled)
      entered.handoff.call (.getStdHandle entered.frame) entered.frame call) :
    RawState.ControlConsistent
      { resume.after.eraseCall entered.handoff.call with control := .caller entered.handoff.record.caller } :=
  ProviderResume.returned_control (record := entered.handoff.record) ran entered.caller resume

/-- The fresh GetStdHandle projection rejects replay and retains the post-read
machine; it need not equal the settled state before the read event. -/
example
    (ran : CallProtocol.return? providerState entered.handoff.call
      entered.handoff.record.caller entered.handoff.record.agent entered.handoff.record.ids =
      some (entered.handoff.record, settled))
    (resume : ProviderResume.Success loaded (ProviderResume.afterReturn before settled)
      entered.handoff.call (.getStdHandle entered.frame) entered.frame call)
    {fresh : CallProtocol.State ApiRequest}
    (packed : resume.after.metadata.pack? resume.after.machine.machine = some fresh) :
    fresh.machine = resume.after.machine.machine ∧
      fresh.pending.lookup entered.handoff.call = none ∧
      CallProtocol.return? fresh entered.handoff.call entered.handoff.record.caller
        entered.handoff.record.agent entered.handoff.record.ids = none :=
  ProviderResume.finalized_protocol (record := entered.handoff.record) ran resume packed

end Grass.Tests.Win32ProviderResumeFinalization
