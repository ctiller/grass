import Grass.Platform.Win32.RawStep

/-!
# Shared log construction for evaluated CALL and checked API handoff

The log proof is independent of the API request and loan list. Each endpoint
adapter supplies its actual checked handoff and computed raw result; all three
use the same CALL and handoff append law. Graph ordering remains explicit and
these adapters do not establish native provider adequacy or complete coverage.
-/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- Derive both log suffixes once from an actual CALL followed by the actual
protocol handoff. The two output equalities are carrier projections, not free
event lists or substitute execution witnesses. -/
theorem call_handoff_appends {before reached : State ApiRequest} {calls : CallRuntimeTable}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Grass.ISA.X86.Execution.CallNormal before.machine
      afterFetch afterRead afterStore displacement)
    (reachedExact : WriteFile.reachedCall? before receipt = some reached)
    {protocol next : CallProtocol.State ApiRequest}
    (projected : reached.callProtocol? = some protocol)
    {caller agent : ContextId} {request : ApiRequest}
    {loans : List CallProtocol.LoanRequest} {call : CallProtocol.CallId}
    (issued : CallProtocol.handoff? protocol caller agent request loans = some (call, next))
    {after : RawState} (machine : after.machine.machine = next.machine)
    (metadata : after.metadata = next.metadata) :
    (Event.between (before.raw calls) after .internal).Appends (before.raw calls) after := by
  have reachedFields := WriteFile.reachedCall?_fields reachedExact
  have projectedFields := State.callProtocol?_fields projected
  have recorded := CallProtocol.handoff?_records issued
  obtain ⟨memory, _, nextMachine⟩ := recorded.2.2.2.2.2
  obtain ⟨fetched, target, saved, appended, _, _, _⟩ := receipt.events_exact
  have machineEvents : after.machine.machine.events =
      before.machine.machine.events ++ [fetched, target, saved] := by
    rw [machine, nextMachine]
    change protocol.machine.events = _
    rw [projectedFields.1, reachedFields.1]
    exact appended
  have beforeMetadata : protocol.metadata = before.metadata :=
    projectedFields.2.trans reachedFields.2.1
  have boundaries := recorded.2.2.2.2.1
  have afterBoundaries : after.metadata.boundaries = before.metadata.boundaries ++
      [.handoff call caller agent
        ((GrantMint.mint protocol.grantSupply
          (loans.map (fun loan => loan.grant caller agent))).1.map Prod.fst)] := by
    rw [metadata]
    change next.boundaries = _
    rw [boundaries]
    rw [← beforeMetadata]
    rfl
  exact Event.between_appends machineEvents afterBoundaries

end Grass.Platform.Win32.Raw

namespace Grass.Platform.Win32.WriteFile.CallHandoff

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader Grass.Platform.Win32.Raw

/-- Construct the raw WriteFile entry using the shared computed log suffix. -/
theorem rawStep {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
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
    {realization : WriteFile.Realization} {environment : ConsoleEnvironment} {graph nextGraph : Graph}
    (prior : graph.WellFormed (before.raw calls))
    (next : nextGraph.WellFormed (entered.rawAfter calls))
    (graphExtends : graph.Extends nextGraph) :
    RawStep loaded realization environment graph (before.raw calls) (.apiEntry (.writeFile request) agent)
      (Event.between (before.raw calls) (entered.rawAfter calls) .internal)
      (entered.rawAfter calls) nextGraph :=
  RawStep.writeFileEntry entered evaluated dispatch selected requestMatches
    ⟨call_handoff_appends receipt entered.reachedExact entered.handoff.projected
      entered.handoff.issued rfl rfl, prior, next, graphExtends⟩ rfl

end Grass.Platform.Win32.WriteFile.CallHandoff

namespace Grass.Platform.Win32.GetStdHandle.CallHandoff

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader Grass.Platform.Win32.Raw

/-- Construct raw GetStdHandle entry with the same shared handoff log law. -/
theorem rawStep {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
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
    {realization : WriteFile.Realization} {environment : ConsoleEnvironment} {graph nextGraph : Graph}
    (prior : graph.WellFormed (before.raw calls))
    (next : nextGraph.WellFormed (entered.afterRaw calls))
    (graphExtends : graph.Extends nextGraph) :
    RawStep loaded realization environment graph (before.raw calls)
      (.apiEntry (.getStdHandle (GetStdHandle.selector entered.reached.machine)) agent)
      (Event.between (before.raw calls) (entered.afterRaw calls) .internal)
      (entered.afterRaw calls) nextGraph :=
  RawStep.getStdHandleEntry entered evaluated dispatch selected requestMatches
    ⟨call_handoff_appends receipt entered.reachedExact entered.handoff.projected
      entered.handoff.issued rfl rfl, prior, next, graphExtends⟩ rfl

end Grass.Platform.Win32.GetStdHandle.CallHandoff

namespace Grass.Platform.Win32.ExitProcess.CallHandoff

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader Grass.Platform.Win32.Raw

/-- Construct the nonreturning API entry using the same log law; this does not
observe termination or give ExitProcess a returning frame. -/
theorem rawStep {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
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
    {realization : WriteFile.Realization} {environment : ConsoleEnvironment} {graph nextGraph : Graph}
    (prior : graph.WellFormed (before.raw calls))
    (next : nextGraph.WellFormed (entered.handoff.initRaw calls))
    (graphExtends : graph.Extends nextGraph) :
    RawStep loaded realization environment graph (before.raw calls)
      (.apiEntry (.exitProcess (ExitProcess.status entered.reached.machine)) agent)
      (Event.between (before.raw calls) (entered.handoff.initRaw calls) .internal)
      (entered.handoff.initRaw calls) nextGraph :=
  RawStep.exitProcessEntry entered evaluated dispatch selected requestMatches
    ⟨call_handoff_appends receipt entered.reachedExact entered.handoff.projected
      entered.handoff.issued rfl rfl, prior, next, graphExtends⟩ rfl

end Grass.Platform.Win32.ExitProcess.CallHandoff
