import Grass.Platform.Win32.RawServiceMetadata

/-! Finite service-prefix preservation for a returning call. Only edges before
the supplied length are required. The original issuance is established by the
consumer's actual CallHandoff; its rawAfter lookup supplies the initial runtime
here. No state/history carrier, infinite extension, or return is constructed. -/

namespace Grass.Platform.Win32.Raw.RawStep

open Grass.Core Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {environment : ConsoleEnvironment}
  {interpretation : WriteFile.ReturnInterpretation}
  {call : CallProtocol.CallId}

/-- An actual service edge updates the accepted frontier while retaining the
original return frame and fifth-argument coordinates at the same runtime key. -/
theorem service_runtime_frame
    {before after : RawState} {graph nextGraph : Graph}
    {agent : ContextId} {action : WriteFile.Action} {event : Event}
    (step : RawStep loaded realization environment interpretation graph before (.providerService call agent action)
      event after nextGraph)
    (runtime : WriteFileRuntime)
    (lookup : before.calls.lookup call = some (.writeFile runtime)) :
    ∃ nextRuntime, after.calls.lookup call = some (.writeFile nextRuntime) ∧
      nextRuntime.toReturnFrame = runtime.toReturnFrame ∧
      nextRuntime.fifthSlot = runtime.fifthSlot ∧ nextRuntime.loanPlan = runtime.loanPlan := by
  obtain ⟨record, output, receipt, _, rfl, _, _, _⟩ := service_receipt step
  have same : receipt.runtime = runtime := CallRuntime.writeFile.inj
    (Option.some.inj (receipt.runtimeLookup.symm.trans lookup))
  exact ⟨receipt.nextRuntime, receipt.after_runtimeLookup,
    receipt.after_frame.trans (congrArg WriteFileRuntime.toReturnFrame same),
    receipt.after_fifth.trans (congrArg WriteFileRuntime.fifthSlot same),
    receipt.after_loanPlan.trans (congrArg WriteFileRuntime.loanPlan same)⟩

/-- Preserve the whole pending record and original runtime frame through a
bounded sequence of actual same-call service edges. In particular the endpoint
lookup is retained for matching a later return. Nothing is assumed at or after
`length`, and the zero-edge case retains the supplied initial witnesses. -/
theorem service_prefix_runtime
    (raw : Nat → RawState) (graph : Nat → Graph)
    (agent : Nat → ContextId) (action : Nat → WriteFile.Action) (event : Nat → Event)
    (length : Nat)
    (steps : ∀ n, n < length → RawStep loaded realization environment interpretation (graph n) (raw n)
      (.providerService call (agent n) (action n)) (event n) (raw (n + 1)) (graph (n + 1)))
    (runtime : WriteFileRuntime)
    (lookup : (raw 0).calls.lookup call = some (.writeFile runtime))
    (record : CallProtocol.Pending WriteFile.Request)
    (pending : (raw 0).metadata.pending.lookup call = some (WriteFile.embedPending record)) :
    ∀ n, n ≤ length →
      (raw n).metadata = (raw 0).metadata ∧
      (raw n).metadata.pending.lookup call = some (WriteFile.embedPending record) ∧
      ∃ currentRuntime, (raw n).calls.lookup call = some (.writeFile currentRuntime) ∧
        currentRuntime.toReturnFrame = runtime.toReturnFrame ∧
        currentRuntime.fifthSlot = runtime.fifthSlot ∧
        currentRuntime.loanPlan = runtime.loanPlan := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨rfl, pending, runtime, lookup, rfl, rfl, rfl⟩
  | succ n ih =>
      intro bounded
      have below : n < length := by omega
      obtain ⟨metadata, _, previous, previousLookup, frame, fifth, plan⟩ := ih (by omega)
      have step := steps n below
      have nextMetadata := (service_metadata step).trans metadata
      obtain ⟨nextRuntime, nextLookup, nextFrame, nextFifth, nextPlan⟩ :=
        service_runtime_frame step previous previousLookup
      refine ⟨nextMetadata, ?_, nextRuntime, nextLookup,
        nextFrame.trans frame, nextFifth.trans fifth, nextPlan.trans plan⟩
      rw [nextMetadata]
      exact pending

end Grass.Platform.Win32.Raw.RawStep
