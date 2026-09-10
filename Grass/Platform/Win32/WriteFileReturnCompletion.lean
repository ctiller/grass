import Grass.Platform.Win32.WriteFileReturn
import Grass.Platform.Win32.CallResumeBinding
import Grass.Platform.Win32.ProviderResumeFinalization

/-! Complete a matched WriteFile return using the exact current provider
endpoint and supplied register observation. Original raw service ancestry is
an operational consumer obligation; the link below is data agreement only.
No responsiveness, native transfer, or complete ABI adequacy is asserted. -/

namespace Grass.Platform.Win32.WriteFile.Return

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {before : ExecutionState.State ApiRequest}
  {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
  {call : CallNormal before.machine afterFetch afterRead afterStore displacement}
  {request : Request} {agent : ContextId}
  {entered : CallHandoff loaded before call request agent}
  {realization : Realization} {provider settled : ProtocolState}
  {frontier : Prefix entered.abi.loanPlan provider entered.handoff.call entered.handoff.record}
  {history : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
    entered.handoff.call entered.handoff.record frontier}
  {selected : ReturnInterpretation} {result : ReturnResult}
  {current : RawState} {gpr : Gpr → BitVec 64} {rflags : BitVec 64}

/-- API-specific endpoint evidence. The current protocol is exactly the
original-indexed history frontier, including its full pending record and
accepted count. The operational consumer must also supply actual raw ancestry. -/
structure Observation (entered : CallHandoff loaded before call request agent)
    {provider : ProtocolState}
    (frontier : Prefix entered.abi.loanPlan provider entered.handoff.call entered.handoff.record)
    (current : RawState) (result : ReturnResult)
    (gpr : Gpr → BitVec 64) (rflags : BitVec 64) where
  projected : current.metadata.pack? current.machine.machine = some provider
  control : current.control = .pending entered.handoff.call entered.handoff.record.caller
    entered.handoff.record.agent
  runtime : WriteFileRuntime
  link : ProviderResume.Link current entered.handoff.call (.writeFile runtime)
    entered.runtime.toReturnFrame call
  fifth : runtime.fifthSlot = entered.runtime.fifthSlot
  plan : runtime.loanPlan = entered.abi.loanPlan
  accepted : runtime.accepted = frontier.accepted
  preserved : ProviderResume.PreservesNonvolatile
    (ProviderResume.observeRegisters current gpr rflags) entered.runtime.toReturnFrame
  output : ProviderResume.WriteFileOutput (ProviderResume.observeRegisters current gpr rflags) result

private theorem afterReturnLink
    (observed : Observation entered frontier current result gpr rflags) (settled : ProtocolState) :
    ProviderResume.Link
      (ProviderResume.afterReturn (ProviderResume.observeRegisters current gpr rflags) settled)
      entered.handoff.call (.writeFile observed.runtime) entered.runtime.toReturnFrame call :=
  { runtimeLookup := observed.link.runtimeLookup
    runtimeFrame := observed.link.runtimeFrame
    entryRsp := observed.link.entryRsp
    continuation := observed.link.continuation
    returnProvenance := observed.link.returnProvenance
    returnRange := observed.link.returnRange }

structure Completion (observed : Observation entered frontier current result gpr rflags)
    (returned : MatchedReturn selected history result settled) where
  resumed : ProviderResume.Success loaded
    (ProviderResume.afterReturn (ProviderResume.observeRegisters current gpr rflags) settled)
    entered.handoff.call (.writeFile observed.runtime) entered.runtime.toReturnFrame call
  resumedExact : ProviderResume.resume loaded
    (ProviderResume.afterReturn (ProviderResume.observeRegisters current gpr rflags) settled)
    entered.handoff.call (.writeFile observed.runtime) entered.runtime.toReturnFrame call
    (ProviderResume.PolicyBinding.ofCallEntry entered.policy)
    (afterReturnLink observed settled) observed.preserved = .ok resumed

/-- Settlement is the actual matched protocol-return equation; only then does
the shared producer read the current returned slot and check its original CALL. -/
def complete? (observed : Observation entered frontier current result gpr rflags)
    (returned : MatchedReturn selected history result settled) :
    Except ProviderResume.Failure (Completion observed returned) :=
  match ran : ProviderResume.resume loaded
      (ProviderResume.afterReturn (ProviderResume.observeRegisters current gpr rflags) settled)
      entered.handoff.call (.writeFile observed.runtime) entered.runtime.toReturnFrame call
      (ProviderResume.PolicyBinding.ofCallEntry entered.policy)
      (afterReturnLink observed settled) observed.preserved with
  | .error reason => .error reason
  | .ok resumed => .ok ⟨resumed, ran⟩

namespace Completion

variable {observed : Observation entered frontier current result gpr rflags}
  {returned : MatchedReturn selected history result settled}

def final (completion : Completion observed returned) : RawState :=
  { completion.resumed.after.eraseCall entered.handoff.call with
    control := .caller entered.handoff.record.caller }

theorem fields (completion : Completion observed returned) :
    completion.final.machine = completion.resumed.after.machine ∧
      completion.final.metadata = settled.metadata ∧
      completion.final.control = .caller entered.handoff.record.caller ∧
      completion.final.calls.lookup entered.handoff.call = none ∧
      ∀ other, other ≠ entered.handoff.call →
        completion.final.calls.lookup other = current.calls.lookup other := by
  have facts := ProviderResume.finalized_fields completion.resumed entered.handoff.record.caller
  refine ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, ?_⟩
  intro other different
  exact (facts.2.2.2.2 other different).trans
    (congrArg (fun calls => calls.lookup other) completion.resumed.raw_frame.2.2)

theorem control (completion : Completion observed returned) :
    RawState.ControlConsistent completion.final :=
  ProviderResume.returned_control (record := embedPending entered.handoff.record)
    returned.ran entered.caller completion.resumed

theorem logs (completion : Completion observed returned) :
    ∃ readEvent, completion.final.machine.machine.events = current.machine.machine.events ++ [readEvent] ∧
      completion.final.metadata.boundaries = current.metadata.boundaries ++
        [.returned entered.handoff.call entered.handoff.record.caller
          entered.handoff.record.agent entered.handoff.record.ids] ∧
      readEvent.event.valueRead = some completion.resumed.slot.receipt.read.observed :=
  ProviderResume.finalized_logs (before := ProviderResume.observeRegisters current gpr rflags)
    (record := embedPending entered.handoff.record)
    returned.ran observed.projected completion.resumed

theorem protocol (completion : Completion observed returned) {protocol : ProtocolState}
    (packed : completion.final.metadata.pack? completion.final.machine.machine = some protocol) :
    protocol.machine = completion.final.machine.machine ∧
      protocol.pending.lookup entered.handoff.call = none ∧
      CallProtocol.return? protocol entered.handoff.call entered.handoff.record.caller
        entered.handoff.record.agent entered.handoff.record.ids = none :=
  ProviderResume.finalized_protocol (record := embedPending entered.handoff.record)
    returned.ran completion.resumed packed

theorem output (completion : Completion observed returned) :
    ProviderResume.WriteFileOutput completion.final result := by
  change (completion.resumed.after.machine.gpr .rax).setWidth 32 = result.rawBool
  rw [completion.resumed.gpr_other .rax (by decide)]
  exact observed.output

theorem memory (completion : Completion observed returned) :
    completion.final.machine.machine.memory = settled.machine.memory :=
  ProviderResume.resume_memory completion.resumed

theorem conforms (completion : Completion observed returned) :
    result.Conforms completion.final.machine.machine.memory entered.handoff.record.request
      frontier.accepted := by
  rw [completion.memory]
  exact returned.conforms_after

end Completion
end Grass.Platform.Win32.WriteFile.Return
