import Grass.Platform.Win32.GetStdHandleResult
import Grass.Platform.Win32.ProviderResumeFinalization

/-! Bounded GetStdHandle return composition from an observed provider register
state.  This is protocol settlement plus the shared slot-read resume candidate;
it makes no native-provider or physical-return claim. -/

namespace Grass.Platform.Win32.GetStdHandle.Return

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

inductive Failure where
  | stageProjection
  | protocolReturn
  | resume (reason : ProviderResume.Failure)

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {environment : ConsoleEnvironment} {before : ExecutionState.State ApiRequest}
  {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
  {call : CallNormal before.machine afterFetch afterRead afterStore displacement}
  {agent : ContextId} {entered : GetStdHandle.CallHandoff loaded before call agent}
  {evaluated : Raw.EvaluatedCall loaded before call} {prior : CallRuntimeTable}
  {gpr : Gpr → BitVec 64} {rflags : BitVec 64}

private theorem afterReturnLink (observed : ProviderResult.Receipt loaded environment entered evaluated prior gpr rflags)
    (settled : CallProtocol.State ApiRequest) :
    ProviderResume.Link (ProviderResume.afterReturn (ProviderResult.stage entered prior gpr rflags) settled)
      entered.handoff.call (.getStdHandle entered.frame) entered.frame call :=
  { runtimeLookup := by simp [ProviderResume.afterReturn]
    runtimeFrame := observed.resumeLink.runtimeFrame
    entryRsp := observed.resumeLink.entryRsp
    continuation := observed.resumeLink.continuation
    returnProvenance := observed.resumeLink.returnProvenance
    returnRange := observed.resumeLink.returnRange }

private theorem afterReturn_preserves
    (observed : ProviderResult.Receipt loaded environment entered evaluated prior gpr rflags)
    (settled : CallProtocol.State ApiRequest) :
    ProviderResume.PreservesNonvolatile
      (ProviderResume.afterReturn (ProviderResult.stage entered prior gpr rflags) settled) entered.frame :=
  observed.preservesNonvolatile

structure Completion {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {environment : ConsoleEnvironment}
    {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {call : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} {entered : GetStdHandle.CallHandoff loaded before call agent}
    {evaluated : Raw.EvaluatedCall loaded before call} {prior : CallRuntimeTable}
    {gpr : Gpr → BitVec 64} {rflags : BitVec 64}
    (observed : ProviderResult.Receipt loaded environment entered evaluated prior gpr rflags) where
  provider : CallProtocol.State ApiRequest
  packed : (ProviderResult.stage entered prior gpr rflags).metadata.pack?
    (ProviderResult.stage entered prior gpr rflags).machine.machine = some provider
  settled : CallProtocol.State ApiRequest
  returned : CallProtocol.return? provider entered.handoff.call entered.handoff.record.caller
    entered.handoff.record.agent entered.handoff.record.ids = some (entered.handoff.record, settled)
  resumed : ProviderResume.Success loaded
    (ProviderResume.afterReturn (ProviderResult.stage entered prior gpr rflags) settled)
    entered.handoff.call (.getStdHandle entered.frame) entered.frame call
  resumedExact : ProviderResume.resume loaded
    (ProviderResume.afterReturn (ProviderResult.stage entered prior gpr rflags) settled)
    entered.handoff.call (.getStdHandle entered.frame) entered.frame call
    (entered.resumeInputs prior).1 (afterReturnLink observed settled)
    (afterReturn_preserves observed settled) = .ok resumed

def complete?
    (observed : ProviderResult.Receipt loaded environment entered evaluated prior gpr rflags) :
    Except Failure (Completion loaded observed) :=
  match packed : (ProviderResult.stage entered prior gpr rflags).metadata.pack?
      (ProviderResult.stage entered prior gpr rflags).machine.machine with
  | none => .error .stageProjection
  | some provider =>
      match returned : CallProtocol.return? provider entered.handoff.call entered.handoff.record.caller
          entered.handoff.record.agent entered.handoff.record.ids with
      | none => .error .protocolReturn
      | some (returnedRecord, settled) => by
          have providerEq : provider = entered.handoff.afterProtocol :=
            Option.some.inj (packed.symm.trans (ProviderResult.stage_pack entered prior gpr rflags))
          have occurrence := (CallProtocol.return?_effects returned).occurrence
          rw [providerEq] at occurrence
          have same : returnedRecord = entered.handoff.record :=
            Option.some.inj (occurrence.symm.trans entered.handoff.recorded)
          let returned : CallProtocol.return? provider entered.handoff.call entered.handoff.record.caller
              entered.handoff.record.agent entered.handoff.record.ids = some (entered.handoff.record, settled) := by
            cases same
            exact returned
          exact match resumeResult : ProviderResume.resume loaded
              (ProviderResume.afterReturn (ProviderResult.stage entered prior gpr rflags) settled)
              entered.handoff.call (.getStdHandle entered.frame) entered.frame call
              (entered.resumeInputs prior).1 (afterReturnLink observed settled)
              (afterReturn_preserves observed settled) with
          | .error reason => .error (.resume reason)
          | .ok success => .ok ⟨provider, packed, settled, returned, success, resumeResult⟩

namespace Completion

variable {observed : ProviderResult.Receipt loaded environment entered evaluated prior gpr rflags}

def final (completion : Completion loaded observed) : RawState :=
  { completion.resumed.after.eraseCall entered.handoff.call with control := .caller entered.handoff.caller }

theorem fields (completion : Completion loaded observed) :
    completion.final.machine = completion.resumed.after.machine ∧
      completion.final.metadata = completion.settled.metadata ∧
      completion.final.control = .caller entered.handoff.caller ∧
      completion.final.calls.lookup entered.handoff.call = none := by
  have full := ProviderResume.finalized_fields completion.resumed entered.handoff.caller
  exact ⟨full.1, full.2.1, full.2.2.1, full.2.2.2.1⟩

theorem other_calls (completion : Completion loaded observed) {other : CallProtocol.CallId}
    (different : other ≠ entered.handoff.call) :
    completion.final.calls.lookup other = completion.resumed.after.calls.lookup other :=
  (ProviderResume.finalized_fields completion.resumed entered.handoff.caller).2.2.2.2 other different

theorem protocol (completion : Completion loaded observed) {protocol : CallProtocol.State ApiRequest}
    (packed : completion.resumed.after.metadata.pack? completion.resumed.after.machine.machine = some protocol) :
    protocol.machine = completion.resumed.after.machine.machine ∧
      protocol.pending.lookup entered.handoff.call = none ∧
      CallProtocol.return? protocol entered.handoff.call entered.handoff.record.caller entered.handoff.record.agent
        entered.handoff.record.ids = none :=
  ProviderResume.finalized_protocol completion.returned completion.resumed packed

theorem control (completion : Completion loaded observed) :
    RawState.ControlConsistent completion.final := by
  apply ProviderResume.returned_control completion.returned
  exact entered.caller

theorem logs (completion : Completion loaded observed) :
    ∃ readEvent, completion.final.machine.machine.events =
      (ProviderResult.stage entered prior gpr rflags).machine.machine.events ++ [readEvent] ∧
      completion.final.metadata.boundaries =
        (ProviderResult.stage entered prior gpr rflags).metadata.boundaries ++
          [.returned entered.handoff.call entered.handoff.record.caller entered.handoff.record.agent
            entered.handoff.record.ids] ∧
      readEvent.event.valueRead = some completion.resumed.slot.receipt.read.observed := by
  exact ProviderResume.finalized_logs completion.returned completion.packed completion.resumed

theorem rax_unchanged (completion : Completion loaded observed) :
    completion.final.machine.gpr .rax = gpr .rax := by
  rw [completion.fields.1, completion.resumed.gpr_other .rax (by decide)]
  exact ProviderResult.stage_rAX entered prior gpr rflags

end Completion
end Grass.Platform.Win32.GetStdHandle.Return
