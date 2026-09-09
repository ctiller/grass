import Grass.Platform.Win32.RawStepSignature
import Grass.Platform.Win32.WriteFileRuntime
import Grass.Platform.Win32.WriteFileService
import Grass.Platform.Win32.GetStdHandleRuntime
import Grass.Platform.Win32.ExitProcessRuntime

/-!
# Concrete raw endpoint case composition

This is the fixed union of the endpoint cases currently implemented, indexed by
one loaded image and one provider realization for an entire derivation. It is
not a complete Windows execution model or a public realization profile. In
particular, native import dispatch, CPU cases, failed/refused provider actions,
physical return and terminal observation are not classified here. No totality,
safety, or endpoint certification follows from this partial case relation.

Entry cases combine the actual CALL and protocol handoff from the exact raw
pre-CALL state. They never select a past CALL receipt at an already reached
callee state. Service cases retain the actual committed action, runtime table,
publication, and causal graph correspondence.
-/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- The provider's selected causal order is exactly the transitive closure of
the raw graph, not a second independently chosen ordering for the same edge. -/
def Graph.Realizes (graph : Graph) (model : WriteFile.CausalModel)
    (state : WriteFile.ProtocolState) : Prop :=
  ∀ left right, model.precedes state left right ↔
    Relation.TransGen (fun a b => (a, b) ∈ graph) left right

/-- Implemented endpoint cases only. The indices fix the image and realization;
neither can be chosen anew by a constructor. Missing dispatch and outcome
coverage prevent using this relation as a certified public execution model. -/
inductive RawStep {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (realization : WriteFile.Realization) :
    StepSignature where
  | writeFileEntry {graph nextGraph : Graph} {event : Event}
      {before : State ApiRequest} {calls : CallRuntimeTable}
      {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
      {receipt : Grass.ISA.X86.Execution.CallNormal before.machine
        afterFetch afterRead afterStore displacement}
      {request : WriteFile.Request} {agent : ContextId}
      (entered : WriteFile.CallHandoff loaded before receipt request agent)
      (agreement : EdgeAgreement graph (before.raw calls) event
        (entered.rawAfter calls) nextGraph)
      (kind : event.kind = .internal) :
      RawStep loaded realization graph (before.raw calls) (.apiEntry (.writeFile request) agent)
        event (entered.rawAfter calls) nextGraph
  | getStdHandleEntry {graph nextGraph : Graph} {event : Event}
      {before : State ApiRequest} {calls : CallRuntimeTable}
      {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
      {receipt : Grass.ISA.X86.Execution.CallNormal before.machine
        afterFetch afterRead afterStore displacement} {agent : ContextId}
      (entered : GetStdHandle.CallHandoff loaded before receipt agent)
      (agreement : EdgeAgreement graph (before.raw calls) event
        (entered.afterRaw calls) nextGraph)
      (kind : event.kind = .internal) :
      RawStep loaded realization graph (before.raw calls)
        (.apiEntry (.getStdHandle (GetStdHandle.selector entered.reached.machine)) agent)
        event (entered.afterRaw calls) nextGraph
  | exitProcessEntry {graph nextGraph : Graph} {event : Event}
      {before : State ApiRequest} {calls : CallRuntimeTable}
      {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
      {receipt : Grass.ISA.X86.Execution.CallNormal before.machine
        afterFetch afterRead afterStore displacement} {agent : ContextId}
      (entered : ExitProcess.CallHandoff loaded before receipt agent)
      (agreement : EdgeAgreement graph (before.raw calls) event
        (entered.handoff.initRaw calls) nextGraph)
      (kind : event.kind = .internal) :
      RawStep loaded realization graph (before.raw calls)
        (.apiEntry (.exitProcess (ExitProcess.status entered.reached.machine)) agent)
        event (entered.handoff.initRaw calls) nextGraph
  | service {graph nextGraph : Graph} {before : RawState} {event : Event}
      {call : CallProtocol.CallId} {record : CallProtocol.Pending WriteFile.Request}
      {action : WriteFile.Action} {output : Vec Byte}
      (receipt : WriteFile.ServiceReceipt realization before call record action output)
      (agreement : EdgeAgreement graph before event receipt.after nextGraph)
      (kind : event.kind = if output.length = 0 then .internal
        else .endpoint (.published call output))
      (priorCausal : graph.Realizes realization.causal receipt.protocol)
      (nextCausal : nextGraph.Realizes realization.causal receipt.nextProtocol) :
      RawStep loaded realization graph before (.providerService call record.agent action)
        event receipt.after nextGraph

namespace RawStep

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {graph nextGraph : Graph} {before after : RawState} {choice : Choice} {event : Event}

/-- Every installed case retains both exact log suffixes and graph obligations. -/
theorem agreement (step : RawStep loaded realization graph before choice event after nextGraph) :
    EdgeAgreement graph before event after nextGraph := by
  cases step <;> assumption

/-- Inversion for the installed service case, not an exhaustive classification
of physical provider activity or all choices admitted by a future profile. -/
theorem service_receipt {call : CallProtocol.CallId} {agent : ContextId}
    {action : WriteFile.Action}
    (step : RawStep loaded realization graph before (.providerService call agent action)
      event after nextGraph) :
    ∃ (record : CallProtocol.Pending WriteFile.Request) (output : Vec Byte)
      (receipt : WriteFile.ServiceReceipt realization before call record action output),
      record.agent = agent ∧ receipt.after = after ∧
      event.kind = (if output.length = 0 then .internal else .endpoint (.published call output)) ∧
      graph.Realizes realization.causal receipt.protocol ∧
      nextGraph.Realizes realization.causal receipt.nextProtocol := by
  cases step with
  | service receipt agreement kind priorCausal nextCausal =>
      exact ⟨_, _, receipt, rfl, rfl, kind, priorCausal, nextCausal⟩

end RawStep
end Grass.Platform.Win32.Raw
