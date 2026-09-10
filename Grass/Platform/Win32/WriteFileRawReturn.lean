import Grass.Platform.Win32.RawStep

/-! Install a checked WriteFile completion from its exact current raw state.
The interpretation is fixed across the relation. Linking the supplied provider
history to an enclosing raw execution remains the outer adapter's obligation;
log suffixes and graph extension alone establish no native causal ordering. -/

namespace Grass.Platform.Win32.WriteFile.Return.Completion

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

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
  {observed : Observation entered frontier current result gpr rflags}
  {returned : MatchedReturn interpretation history result settled}

/-- Canonical logs of the current-state completion, retaining the raw BOOL. -/
def event (completion : Completion observed returned) : Raw.Event :=
  Raw.Event.between current completion.final
    (.endpoint (.apiReturned entered.handoff.call result))

theorem event_appends (completion : Completion observed returned) :
    completion.event.Appends current completion.final := by
  obtain ⟨readEvent, memory, boundaries, _⟩ := completion.logs
  exact Raw.Event.between_appends memory boundaries

theorem event_exact (completion : Completion observed returned) :
    ∃ readEvent, completion.event.memory = [readEvent] ∧
      completion.event.boundaries =
        [.returned entered.handoff.call entered.handoff.record.caller
          entered.handoff.record.agent entered.handoff.record.ids] ∧
      readEvent.event.valueRead = some completion.resumed.slot.receipt.read.observed := by
  obtain ⟨readEvent, memory, boundaries, value⟩ := completion.logs
  have suffixes := Raw.Event.between_suffixes (kind :=
    .endpoint (.apiReturned entered.handoff.call result)) memory boundaries
  exact ⟨readEvent, suffixes.1, suffixes.2, value⟩

/-- Build the partial edge using the actual completion equation and evaluated
original CALL. Graph premises concern these exact endpoints. -/
theorem rawStep (completion : Completion observed returned)
    (completed : complete? observed returned = .ok completion)
    (evaluated : Raw.EvaluatedCall loaded before call)
    (caller : environment.caller = entered.handoff.record.caller)
    (providerContext : environment.provider = entered.handoff.record.agent)
    {graph nextGraph : Raw.Graph}
    (priorGraph : graph.WellFormed current)
    (nextWellFormed : nextGraph.WellFormed completion.final)
    (extendsGraph : graph.Extends nextGraph) :
    Raw.RawStep loaded realization environment interpretation graph current
      (.providerReturn entered.handoff.call result gpr rflags)
      completion.event completion.final nextGraph :=
  Raw.RawStep.writeFileReturn evaluated observed returned completion completed caller providerContext
    ⟨completion.event_appends, priorGraph, nextWellFormed, extendsGraph⟩

end Grass.Platform.Win32.WriteFile.Return.Completion
