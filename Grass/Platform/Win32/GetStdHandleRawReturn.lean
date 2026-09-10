import Grass.Platform.Win32.RawStep

/-! Install the checked GetStdHandle completion as a partial raw edge from the
original pending carrier. Supplied GPR/RFLAGS data belongs to the explicit
choice; the internal staged register state is never the edge's prestate.
The exact return/read log suffix is derived from the completion. Graph
well-formedness and extension do not establish cross-log or native causal
ordering; that correspondence remains owed.
-/

namespace Grass.Platform.Win32.GetStdHandle.Return.Completion

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {environment : ConsoleEnvironment} {before : ExecutionState.State ApiRequest}
  {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
  {call : CallNormal before.machine afterFetch afterRead afterStore displacement}
  {agent : ContextId} {entered : GetStdHandle.CallHandoff loaded before call agent}
  {evaluated : Raw.EvaluatedCall loaded before call} {prior : CallRuntimeTable}
  {gpr : Gpr → BitVec 64} {rflags : BitVec 64}
  {observed : ProviderResult.Receipt loaded environment entered evaluated prior gpr rflags}

/-- Canonical suffix of the actual pending-to-completed edge. The observed raw
handle may be NULL or INVALID; this event grants no handle rights. -/
def event (completion : Completion loaded observed) : Raw.Event :=
  Raw.Event.between (entered.afterRaw prior) completion.final
    (.endpoint (.stdoutAcquired entered.handoff.call (gpr .rax)))

theorem event_appends (completion : Completion loaded observed) :
    completion.event.Appends (entered.afterRaw prior) completion.final := by
  obtain ⟨readEvent, memory, boundaries, _⟩ := completion.logs
  exact Raw.Event.between_appends memory boundaries

/-- The event retains the exact settled occurrence and the actual resumed
slot read, without manufacturing a causal order between the two logs. -/
theorem event_exact (completion : Completion loaded observed) :
    ∃ readEvent, completion.event.memory = [readEvent] ∧
      completion.event.boundaries =
        [.returned entered.handoff.call entered.handoff.record.caller
          entered.handoff.record.agent entered.handoff.record.ids] ∧
      readEvent.event.valueRead = some completion.resumed.slot.receipt.read.observed := by
  obtain ⟨readEvent, memory, boundaries, value⟩ := completion.logs
  change completion.final.machine.machine.events =
    (entered.afterRaw prior).machine.machine.events ++ [readEvent] at memory
  change completion.final.metadata.boundaries =
    (entered.afterRaw prior).metadata.boundaries ++ _ at boundaries
  exact ⟨readEvent, by simp [event, Raw.Event.between, memory],
    by simp [event, Raw.Event.between, boundaries], value⟩

theorem rflags_unchanged (completion : Completion loaded observed) :
    completion.final.machine.rflags = rflags := completion.resumed.rflags_exact

/-- `rawStep` consumes the evaluated completion and derives log agreement.
Its remaining graph premises concern this exact edge and claim no totality. -/
theorem rawStep (completion : Completion loaded observed)
    (completed : complete? observed = .ok completion)
    {realization : WriteFile.Realization} {graph nextGraph : Raw.Graph}
    (priorGraph : graph.WellFormed (entered.afterRaw prior))
    (nextWellFormed : nextGraph.WellFormed completion.final)
    (extendsGraph : graph.Extends nextGraph) :
    Raw.RawStep loaded realization environment graph (entered.afterRaw prior)
      (.stdoutResult entered.handoff.call gpr rflags) completion.event completion.final nextGraph :=
  Raw.RawStep.getStdHandleReturn observed completion completed
    ⟨completion.event_appends, priorGraph, nextWellFormed, extendsGraph⟩

end Grass.Platform.Win32.GetStdHandle.Return.Completion
