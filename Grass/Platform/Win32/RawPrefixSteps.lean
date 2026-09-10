import Grass.Platform.Win32.RawPrefix
import Grass.Semantics.ExecutionSteps

/-! Existential indexed witnesses of the existing finite raw prefix. This
unwraps universe lifts only. Choices are not unique or canonical; a later
service-segment proof must establish its pending phases and original entry. -/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- An admitted loader-rooted prefix decomposes into actual raw edges with
exact indexed events, root and endpoint. It supplies no service classification. -/
theorem prefix_indexed_witnesses {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)}
    (execution : (system loaded realization environment interpretation covered).ExecutionPrefix) :
    ∃ (states : Fin (execution.events.length + 1) → RawState)
      (graphs : Fin (execution.events.length + 1) → Graph)
      (choices : Fin execution.events.length → Choice),
      states ⟨0, Nat.zero_lt_succ _⟩ = initialState loaded covered ∧
      graphs ⟨0, Nat.zero_lt_succ _⟩ = [] ∧
      states ⟨execution.events.length, Nat.lt_succ_self _⟩ = execution.state.down ∧
      graphs ⟨execution.events.length, Nat.lt_succ_self _⟩ = execution.graph.down ∧
      ∀ index : Fin execution.events.length,
        RawStep loaded realization environment interpretation
          (graphs index.castSucc) (states index.castSucc) (choices index)
          (execution.events.get index).down (states index.succ) (graphs index.succ) := by
  obtain ⟨states, graphs, choices, first, firstGraph, last, lastGraph, steps⟩ :=
    execution.runs.steps.exists_indexed_witnesses
  obtain ⟨root, rootGraph⟩ := prefix_initial execution
  exact ⟨fun index => (states index).down, fun index => (graphs index).down, choices,
    (congrArg ULift.down first).trans root, (congrArg ULift.down firstGraph).trans rootGraph,
    congrArg ULift.down last, congrArg ULift.down lastGraph, steps⟩

end Grass.Platform.Win32.Raw
