import Grass.Platform.Win32.WriteFileRawReturn
import Tests.Platform.Win32RawStep
import Tests.Platform.Win32MatchedReturn

/-!
# Conditional WriteFile raw-return adapter regression

This checks the generic installation contract from an already checked
completion.  Its hypotheses retain the selected interpretation and causal
matched return; it does not turn the service-only `noEffects` fixture into a
physical return or native execution claim.
-/

namespace Grass.Tests.Win32WriteFileRawReturn

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState
open Grass.Platform.Win32.WriteFile

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {environment : ConsoleEnvironment} {interpretation : ReturnInterpretation}
  {before : ExecutionState.State ApiRequest}
  {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
  {call : CallNormal before.machine afterFetch afterRead afterStore displacement}
  {request : Request} {agent : ContextId}
  {entered : CallHandoff loaded before call request agent}
  {realization : Realization} {provider settled : ProtocolState}
  {frontier : Prefix entered.abi.loanPlan provider entered.handoff.call entered.handoff.record}
  {history : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
    entered.handoff.call entered.handoff.record frontier}
  {result : ReturnResult} {current : RawState} {gpr : Gpr → BitVec 64} {rflags : BitVec 64}
  {observed : Return.Observation entered frontier current result gpr rflags}
  {returned : MatchedReturn interpretation history result settled}

/-- The public adapter installs the exact checked completion as an edge with
the same fixed interpretation and unmodified provider result. -/
theorem installedStep (completion : Return.Completion observed returned)
    (completed : Return.complete? observed returned = .ok completion)
    (evaluated : Raw.EvaluatedCall loaded before call)
    (caller : environment.caller = entered.handoff.record.caller)
    (providerContext : environment.provider = entered.handoff.record.agent) :
    Raw.RawStep loaded realization environment interpretation [] current
      (.providerReturn entered.handoff.call result gpr rflags)
      completion.event completion.final [] :=
  completion.rawStep completed evaluated caller providerContext
    (Grass.Tests.Win32RawStep.empty_graph_valid _)
    (Grass.Tests.Win32RawStep.empty_graph_valid _) (Raw.Graph.extends_refl [])

theorem installed_retains_provider_result
    (completion : Return.Completion observed returned)
    (completed : Return.complete? observed returned = .ok completion)
    (evaluated : Raw.EvaluatedCall loaded before call)
    (caller : environment.caller = entered.handoff.record.caller)
    (providerContext : environment.provider = entered.handoff.record.agent) :
    ProviderResume.WriteFileOutput completion.final result ∧
      completion.final.machine.rflags = rflags ∧
      completion.event.kind = .endpoint (.apiReturned entered.handoff.call result) ∧
      completion.final.calls.lookup entered.handoff.call = none ∧
      completion.final.ControlConsistent :=
  (installedStep completion completed evaluated caller providerContext).provider_result

theorem installed_retains_exact_suffix
    (completion : Return.Completion observed returned) :
    completion.event.Appends current completion.final ∧
      ∃ readEvent, completion.event.memory = [readEvent] ∧
        completion.event.boundaries =
          [.returned entered.handoff.call entered.handoff.record.caller
            entered.handoff.record.agent entered.handoff.record.ids] ∧
        readEvent.event.valueRead = some completion.resumed.slot.receipt.read.observed :=
  ⟨completion.event_appends, completion.event_exact⟩

/-- Failure carries no count.  A nonzero BOOL, including the unnormalized value
2, cannot be paired with `none`; the raw bits are not coerced to one. -/
def failed : ReturnResult := ⟨0, none⟩
def noncanonicalSuccess : ReturnResult := ⟨2, none⟩

theorem failure_without_count_conforms :
    failed.Conforms Grass.Tests.Win32WriteFile.memory
      Grass.Tests.Win32WriteFile.request 0 := by
  simp [failed, ReturnResult.Conforms]

theorem nonzero_without_count_rejected :
    ¬ noncanonicalSuccess.Conforms Grass.Tests.Win32WriteFile.memory
      Grass.Tests.Win32WriteFile.request 0 := by
  simp [noncanonicalSuccess, ReturnResult.Conforms]

theorem noncanonical_bool_is_retained : noncanonicalSuccess.rawBool = 2 := rfl

end Grass.Tests.Win32WriteFileRawReturn
