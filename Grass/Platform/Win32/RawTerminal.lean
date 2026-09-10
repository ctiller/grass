import Grass.Platform.Win32.RawPrefix

/-! Exact completed-exit evidence at terminal raw frontiers. -/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- Any actual raw edge whose target has terminal control is precisely a
checked `ExitProcess` completion. This is an inversion of the installed raw
relation; it does not assert native cleanup or discharged obligations. -/
theorem RawStep.terminal_target {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {graph nextGraph : Graph} {before after : RawState} {choice : Choice} {event : Event}
    {call : CallProtocol.CallId} {status : BitVec 32}
    (step : RawStep loaded realization environment interpretation graph before choice event after nextGraph)
    (terminal : after.control = .terminal call status) :
    ∃ (observed : ExitProcess.Observation)
      (completion : ExitProcess.Completion environment before observed),
      ExitProcess.complete? environment before observed = some completion ∧
      observed.process = environment.process ∧ observed.call = call ∧
      observed.status = status ∧ completion.after = after ∧
      choice = .exitObservation observed.call observed.status ∧
      event.kind = .endpoint (.processExited observed.call observed.status) := by
  cases step with
  | writeFileEntry entered evaluated dispatch selected requestMatches agreement kind => cases terminal
  | getStdHandleEntry entered evaluated dispatch selected requestMatches agreement kind => cases terminal
  | writeFileReturn evaluated observed returned completion completed caller providerContext agreement =>
      cases terminal
  | getStdHandleReturn observed completion completed agreement => cases terminal
  | exitProcessEntry entered evaluated dispatch selected requestMatches agreement kind => cases terminal
  | completedExit completion completed agreement =>
      cases terminal
      exact ⟨_, completion, completed, completion.processExact, rfl, rfl, rfl, rfl, rfl⟩
  | service receipt agreement kind priorCausal nextCausal =>
      exact Control.noConfusion (receipt.after_control.symm.trans terminal)
  | cpuCompleted control selected evaluated completed agreement kind =>
      exact Control.noConfusion (control.symm.trans terminal)
  | cpuFailure control selected evaluated mapped agreement kind =>
      exact Control.noConfusion (control.symm.trans terminal)
  | cpuUncovered control selected nonNormal evaluated agreement kind =>
      exact Control.noConfusion (control.symm.trans terminal)

/-- A loader-rooted finite prefix can reach terminal control only through a
last actual completed-exit edge. The preceding run and its exact trace are
retained; no earlier execution is reconstructed or selected. -/
theorem terminal_prefix_last_completedExit {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)}
    (execution : (system loaded realization environment interpretation covered).ExecutionPrefix)
    {call : CallProtocol.CallId} {status : BitVec 32}
    (terminal : execution.state.down.control = .terminal call status) :
    ∃ (priorState : RawState) (priorGraph : Graph) (priorEvents : List (ULift.{1} Event))
      (choice : Choice) (event : Event) (observed : ExitProcess.Observation)
      (completion : ExitProcess.Completion environment priorState observed),
      execution.events = priorEvents ++ [ULift.up event] ∧
      (system loaded realization environment interpretation covered).Runs
        execution.initialState execution.initialGraph (ULift.up priorState)
          (ULift.up priorGraph) priorEvents ∧
      RawStep loaded realization environment interpretation priorGraph priorState choice event
        execution.state.down execution.graph.down ∧
      ExitProcess.complete? environment priorState observed = some completion ∧
      observed.process = environment.process ∧ observed.call = call ∧
      observed.status = status ∧ completion.after = execution.state.down ∧
      choice = .exitObservation observed.call observed.status ∧
      event.kind = .endpoint (.processExited observed.call observed.status) := by
  cases execution with
  | mk initialState initialGraph state graph events runs =>
      cases runs with
      | initial valid =>
          have root := valid.1
          rw [root] at terminal
          exact Control.noConfusion terminal
      | @step priorState priorGraph priorEvents choice liftedEvent nextState nextGraph prior step =>
          obtain ⟨observed, completion, completed, process, observedCall, observedStatus,
            after, selectedChoice, kind⟩ := RawStep.terminal_target step terminal
          exact ⟨priorState.down, priorGraph.down, priorEvents, choice, liftedEvent.down,
            observed, completion, rfl, prior, step, completed, process, observedCall,
            observedStatus, after, selectedChoice, kind⟩

end Grass.Platform.Win32.Raw
