import Grass.Platform.Win32.CallResumeHistory
import Grass.Platform.Win32.WriteFileReturnCompletion

/-! Bind matched-return evidence to the constructed finite service history.
Both histories must share this original CallHandoff. Recovering that original
handoff from an enclosing execution remains an outer consistency obligation. -/

namespace Grass.Platform.Win32.WriteFile.CallHandoff

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Raw

/-- Current protocol projection and the same runtime lookup fix the endpoint
and accepted frontier of the constructed history. Its common original root
then fixes the exact causal event suffix. No derivation equality is assumed. -/
theorem returnedAfterService
    {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded before receipt request provider) (prior : CallRuntimeTable)
    {realization : Realization} {environment : ConsoleEnvironment} {interpretation : ReturnInterpretation}
    (raw : Nat → RawState) (graph : Nat → Graph)
    (agent : Nat → ContextId) (action : Nat → Action) (event : Nat → Event)
    (length : Nat) (root : raw 0 = entered.rawAfter prior)
    (steps : ∀ n, n < length → RawStep loaded realization environment interpretation
      (graph n) (raw n) (.providerService entered.handoff.call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1)))
    (causal : HandoffCausality realization.causal entered.handoff.call entered.handoff.record
      entered.handoff.beforeProtocol entered.handoff.afterProtocol)
    {providerState settled : ProtocolState}
    {frontier : Prefix entered.abi.loanPlan providerState entered.handoff.call entered.handoff.record}
    {history : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
      entered.handoff.call entered.handoff.record frontier}
    {result : ReturnResult} {gpr : Gpr → BitVec 64} {rflags : BitVec 64}
    (observed : Return.Observation entered frontier (raw length) result gpr rflags)
    (returned : MatchedReturn interpretation history result settled) :
    MatchedReturn interpretation
      (entered.serviceHistory prior raw graph agent action event length root steps causal).2.2.val
      result settled := by
  let folded := entered.serviceHistory prior raw graph agent action event length root steps causal
  have endpoint : providerState = folded.1 :=
    Option.some.inj (observed.projected.symm.trans folded.2.2.property.1)
  have accepted : folded.2.1.accepted = frontier.accepted := by
    obtain ⟨runtime, lookup, _, accepted⟩ := folded.2.2.property.2
    have same : runtime = observed.runtime :=
      CallRuntime.writeFile.inj (Option.some.inj (lookup.symm.trans observed.link.runtimeLookup))
    exact accepted.symm.trans ((congrArg WriteFileRuntime.accepted same).trans observed.accepted)
  cases endpoint
  exact returned.on_history folded.2.2.val accepted

end Grass.Platform.Win32.WriteFile.CallHandoff
