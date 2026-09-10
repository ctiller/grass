import Grass.Refinement.Console.WriteFileResume
import Grass.Op.CallProtocolSettlement

/-! Mechanical finalization of the actual post-slot-read candidate. These laws
do not install a raw transition or assert physical provider transfer. -/

namespace Grass.Refinement.Console.WriteFileResume

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {callBefore : State}
  {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
  {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
  {before : RawState} {settled : ProtocolState} {callId : CallProtocol.CallId}
  {runtime : CallRuntime} {frame : ReturnFrame}

/-- Compatibility doors for the single API-independent proof implementation. -/
abbrev resume_pack := @ProviderResume.resume_pack

abbrev resume_caller_registered := @ProviderResume.resume_caller_registered

abbrev finalized_fields := @ProviderResume.finalized_fields

abbrev finalized_control := @ProviderResume.finalized_control

/-- Both edge suffixes come from the actual protocol return and slot read.
No ordering edge between those logs is synthesized here. -/
theorem finalized_logs
    {plan : LoanPlan} {realization : Realization} {initial providerState : ProtocolState}
    {record : CallProtocol.Pending Request} {frontier : Prefix plan providerState callId record}
    {history : History plan realization initial callId record frontier}
    {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : MatchedReturn selected history result settled)
    (projected : before.metadata.pack? before.machine.machine = some providerState)
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call) :
    let final := { resume.after.eraseCall callId with control := .caller record.caller }
    ∃ readEvent, final.machine.machine.events = before.machine.machine.events ++ [readEvent] ∧
      final.metadata.boundaries = before.metadata.boundaries ++
        [.returned callId record.caller record.agent record.ids] ∧
      readEvent.event.valueRead = some resume.slot.receipt.read.observed :=
  ProviderResume.finalized_logs (record := embedPending record) returned.ran projected resume

/-- Every successful fresh projection retains the actual post-read machine and
the consumed pending occurrence. Replaying its protocol return is rejected. -/
theorem finalized_protocol
    {plan : LoanPlan} {realization : Realization} {initial providerState : ProtocolState}
    {record : CallProtocol.Pending Request} {frontier : Prefix plan providerState callId record}
    {history : History plan realization initial callId record frontier}
    {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : MatchedReturn selected history result settled)
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call)
    {protocol : ProtocolState}
    (packed : resume.after.metadata.pack? resume.after.machine.machine = some protocol) :
    protocol.machine = resume.after.machine.machine ∧
      protocol.pending.lookup callId = none ∧
      CallProtocol.return? protocol callId record.caller record.agent record.ids = none :=
  ProviderResume.finalized_protocol (record := embedPending record) returned.ran resume packed

/-- The actual matched return discharges caller suspension. The original
handoff identifies the fixed Windows caller; no new readiness premise is added. -/
theorem returned_control
    {original : ExecutionState.State ApiRequest}
    {receipt : CallNormal original.machine afterFetch afterTarget afterCall displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded original receipt request provider)
    {realization : Realization} {providerState : ProtocolState}
    {frontier : Prefix entered.abi.loanPlan providerState entered.handoff.call entered.handoff.record}
    {history : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
      entered.handoff.call entered.handoff.record frontier}
    {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : MatchedReturn selected history result settled)
    {currentRuntime : WriteFileRuntime}
    (resume : ProviderResume.Success loaded (afterReturn before settled) entered.handoff.call
      (.writeFile currentRuntime) entered.runtime.toReturnFrame receipt) :
    RawState.ControlConsistent
      { resume.after.eraseCall entered.handoff.call with control := .caller entered.handoff.record.caller } :=
  ProviderResume.returned_control (record := embedPending entered.handoff.record) returned.ran entered.caller resume

end Grass.Refinement.Console.WriteFileResume
