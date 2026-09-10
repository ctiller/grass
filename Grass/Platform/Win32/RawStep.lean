import Grass.Platform.Win32.RawStepSignature
import Grass.Platform.Win32.WriteFileRuntime
import Grass.Platform.Win32.WriteFileService
import Grass.Platform.Win32.GetStdHandleRuntime
import Grass.Platform.Win32.ExitProcessRuntime
import Grass.Platform.Win32.ApiDispatch

/-!
# Concrete raw endpoint case composition

This is the fixed union of the endpoint cases currently implemented, indexed by
one loaded image and one provider realization for an entire derivation. It is
not a complete Windows execution model or a public realization profile. In
particular, native export adequacy, failed/refused provider actions,
physical return and terminal observation are not classified here. No totality,
safety, or endpoint certification follows from this partial case relation.

Entry cases combine the actual CALL and protocol handoff from the exact raw
pre-CALL state. They never select a past CALL receipt at an already reached
callee state. Service cases retain the actual committed action, runtime table,
publication, and causal graph correspondence. Entry dispatch is selected from
the loaded import layout using the actual CALL effective address and target;
logical selection is not proof of native DLL/export identity.
-/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- The handoff's exact CALL receipt was returned by the fixed checked
evaluator under the selected Windows policy. Standalone success data is not
evaluation provenance. Heterogeneous equality retains the indexed intermediate
states rather than replacing the handoff receipt with a similar CALL. -/
structure EvaluatedCall {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (before : State ApiRequest)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Grass.ISA.X86.Execution.CallNormal before.machine
      afterFetch afterRead afterStore displacement) where
  policy : Grass.ISA.X86.Execution.CpuAccessPolicy
  selected : Cpu.policy? loaded before.machine = some policy
  flags : Grass.ISA.X86.RegisterSemantics.Flags Bool
  success : Grass.ISA.X86.Execution.CallFactory.Success policy before.machine
  evaluated : Grass.ISA.X86.Execution.CheckedExecution.normal policy before.machine flags =
    some (.ok (.call success))
  receiptExact : HEq success.receipt receipt

/-- The provider's selected causal order is exactly the transitive closure of
the raw graph, not a second independently chosen ordering for the same edge. -/
def Graph.Realizes (graph : Graph) (model : WriteFile.CausalModel)
    (state : WriteFile.ProtocolState) : Prop :=
  ∀ left right, model.precedes state left right ↔
    Relation.TransGen (fun a b => (a, b) ∈ graph) left right

/-- Implemented endpoint cases only. The indices fix the image and realization;
neither can be chosen anew by a constructor. Missing native adequacy and outcome
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
      (evaluated : EvaluatedCall loaded before receipt)
      (dispatch : ApiDispatch.Binding loaded
        (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt) receipt.read.value)
      (selected : ApiDispatch.select? loaded
        (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt)
        receipt.read.value = some dispatch)
      (requestMatches : dispatch.MatchesRequest (.writeFile request))
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
      (evaluated : EvaluatedCall loaded before receipt)
      (dispatch : ApiDispatch.Binding loaded
        (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt) receipt.read.value)
      (selected : ApiDispatch.select? loaded
        (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt)
        receipt.read.value = some dispatch)
      (requestMatches : dispatch.MatchesRequest
        (.getStdHandle (GetStdHandle.selector entered.reached.machine)))
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
      (evaluated : EvaluatedCall loaded before receipt)
      (dispatch : ApiDispatch.Binding loaded
        (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt) receipt.read.value)
      (selected : ApiDispatch.select? loaded
        (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt)
        receipt.read.value = some dispatch)
      (requestMatches : dispatch.MatchesRequest
        (.exitProcess (ExitProcess.status entered.reached.machine)))
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
  | cpuCompleted {graph nextGraph : Graph} {before : RawState} {event : Event}
      {policy : Grass.ISA.X86.Execution.CpuAccessPolicy}
      {flags : Grass.ISA.X86.RegisterSemantics.Flags Bool}
      {success : Grass.ISA.X86.Execution.CheckedExecution.Success policy before.machine}
      {result : Grass.ISA.X86.Execution.State}
      (control : before.control = .caller policy.context)
      (selected : Cpu.policy? loaded before.machine = some policy)
      (evaluated : Grass.ISA.X86.Execution.CheckedExecution.normal policy before.machine flags =
        some (.ok success))
      (completed : success.outcome = .progressed result .completed)
      (agreement : EdgeAgreement graph before event (before.withMachine result) nextGraph)
      (kind : event.kind = .cpu .completed) :
      RawStep loaded realization graph before (.cpu (.normal flags)) event
        (before.withMachine result) nextGraph
  | cpuFailure {graph nextGraph : Graph} {before : RawState} {event : Event}
      {policy : Grass.ISA.X86.Execution.CpuAccessPolicy}
      {flags : Grass.ISA.X86.RegisterSemantics.Flags Bool}
      {failure : Grass.ISA.X86.Execution.CheckedExecution.Failure}
      {reached : Grass.ISA.X86.Execution.State}
      {reason : Grass.ISA.X86.Execution.ApplicabilityFailure}
      (control : before.control = .caller policy.context)
      (selected : Cpu.policy? loaded before.machine = some policy)
      (evaluated : Grass.ISA.X86.Execution.CheckedExecution.normal policy before.machine flags =
        some (.error failure))
      (mapped : failure.outcome = some (.outsideProfile reached reason))
      (agreement : EdgeAgreement graph before event (before.withMachine reached) nextGraph)
      (kind : event.kind = .outsideProfile (.checked failure)) :
      RawStep loaded realization graph before (.cpu (.normal flags)) event
        (before.withMachine reached) nextGraph
  | cpuUncovered {graph nextGraph : Graph} {before : RawState} {event : Event}
      {policy : Grass.ISA.X86.Execution.CpuAccessPolicy}
      {choice : Grass.ISA.X86.Execution.CheckedChoice}
      {reached : Grass.ISA.X86.Execution.State}
      {reason : Grass.ISA.X86.Execution.ApplicabilityFailure}
      (control : before.control = .caller policy.context)
      (selected : Cpu.policy? loaded before.machine = some policy)
      (nonNormal : ∀ flags, choice ≠ .normal flags)
      (evaluated : Grass.ISA.X86.Execution.CheckedExecution.evaluate policy before.machine choice =
        some (.outsideProfile reached reason))
      (agreement : EdgeAgreement graph before event (before.withMachine reached) nextGraph)
      (kind : event.kind = .outsideProfile (.cpu reason)) :
      RawStep loaded realization graph before (.cpu choice) event
        (before.withMachine reached) nextGraph

namespace RawStep

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {graph nextGraph : Graph} {before after : RawState} {choice : Choice} {event : Event}

/-- Every installed case retains both exact log suffixes and graph obligations. -/
theorem agreement (step : RawStep loaded realization graph before choice event after nextGraph) :
    EdgeAgreement graph before event after nextGraph := by
  cases step <;> assumption

/-- `cpu_checked` proves that every installed CPU edge is an actual fixed-policy
evaluator result retaining the original non-CPU data, even if metadata cannot pack. -/
theorem cpu_checked {cpuChoice : Grass.ISA.X86.Execution.CheckedChoice}
    (step : RawStep loaded realization graph before (.cpu cpuChoice) event after nextGraph) :
    ∃ (policy : Grass.ISA.X86.Execution.CpuAccessPolicy)
      (outcome : Grass.ISA.X86.Execution.CpuOutcome),
      before.control = .caller policy.context ∧
      Cpu.policy? loaded before.machine = some policy ∧
      Grass.ISA.X86.Execution.CheckedExecution.CheckedStep policy before.machine cpuChoice outcome ∧
      after = before.withMachine outcome.state := by
  cases step with
  | cpuCompleted control selected evaluated completed agreement kind =>
      have checked := Grass.ISA.X86.Execution.CheckedExecution.normal_success evaluated
      rw [completed] at checked
      exact ⟨_, _, control, selected, checked, rfl⟩
  | cpuFailure control selected evaluated mapped agreement kind =>
      exact ⟨_, _, control, selected,
        Grass.ISA.X86.Execution.CheckedExecution.normal_failure evaluated mapped, rfl⟩
  | cpuUncovered control selected nonNormal evaluated agreement kind =>
      exact ⟨_, _, control, selected, evaluated, rfl⟩

/-- `cpu_rejected` proves that choices rejected by the checked evaluator cannot
acquire a raw CPU edge. -/
theorem cpu_rejected {cpuChoice : Grass.ISA.X86.Execution.CheckedChoice}
    {policy : Grass.ISA.X86.Execution.CpuAccessPolicy}
    (selected : Cpu.policy? loaded before.machine = some policy)
    (rejected : Grass.ISA.X86.Execution.CheckedExecution.evaluate policy before.machine cpuChoice = none) :
    ¬ RawStep loaded realization graph before (.cpu cpuChoice) event after nextGraph := by
  intro step
  obtain ⟨actual, outcome, _, actualSelected, checked, _⟩ := step.cpu_checked
  have same : actual = policy := Option.some.inj (actualSelected.symm.trans selected)
  subst actual
  change Grass.ISA.X86.Execution.CheckedExecution.evaluate policy before.machine cpuChoice =
    some outcome at checked
  rw [rejected] at checked
  contradiction

/-- Every installed entry uses a successful computed logical import selection
whose API variant matches the explicit choice. Native identity remains separate. -/
theorem entry_binding {request : ApiRequest} {agent : ContextId}
    (step : RawStep loaded realization graph before (.apiEntry request agent)
      event after nextGraph) :
    ∃ (address target : BitVec 64) (binding : ApiDispatch.Binding loaded address target),
      ApiDispatch.select? loaded address target = some binding ∧
      binding.MatchesRequest request := by
  cases step with
  | writeFileEntry entered evaluated dispatch selected requestMatches agreement kind =>
      exact ⟨_, _, dispatch, selected, requestMatches⟩
  | getStdHandleEntry entered evaluated dispatch selected requestMatches agreement kind =>
      exact ⟨_, _, dispatch, selected, requestMatches⟩
  | exitProcessEntry entered evaluated dispatch selected requestMatches agreement kind =>
      exact ⟨_, _, dispatch, selected, requestMatches⟩

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
