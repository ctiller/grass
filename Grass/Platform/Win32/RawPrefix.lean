import Grass.Platform.Win32.RawStep
import Grass.Semantics.Execution

/-! The relational system for the fixed raw execution relation. Its root is
computed from the exact loaded machine and fresh protocol supply. Terminal
states retain the actual exit call and status; all pointwise actual infinite
runs are admitted, without fairness or responsiveness requirements. This is a
relative operational system, not native adequacy or a full BehaviorModel:
faithful external waiting and its public observation mapping remain separate.
The existing system uses one universe while raw choices occupy Type 1. ULift
on events, states and graphs only aligns universes; Step unwraps them exactly.
-/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- The exact loaded machine with fresh call bookkeeping and the loaded caller;
the supplied coverage proof licenses the actual initial grant supply. -/
def initialState {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs)
    (covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)) : RawState :=
  let protocol : CallProtocol.State ApiRequest :=
    CallProtocol.initial loaded.initialState.machine .initial covered
  (ExecutionState.State.ofCallProtocol protocol loaded.initialState rfl
    (.caller inputs.thread)).raw

/-- The computed loader root has a live, unsuspended caller in the checked
protocol view. It does not establish that the first instruction can execute. -/
theorem initialState_controlConsistent {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs)
    (covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)) :
    (initialState loaded covered).ControlConsistent := by
  let protocol : CallProtocol.State ApiRequest :=
    CallProtocol.initial loaded.initialState.machine .initial covered
  let checked := ExecutionState.State.ofCallProtocol protocol loaded.initialState rfl
    (.caller inputs.thread)
  refine ⟨checked, State.raw_checked? checked _, ?_⟩
  change ∃ packed, checked.callProtocol? = some packed ∧
    (∃ kind, packed.machine.contexts.lookup inputs.thread = some kind) ∧
      CallProtocol.callerPending packed inputs.thread = false
  refine ⟨protocol, State.ofCallProtocol_callProtocol? _ _ _ _, ⟨.thread, loaded.environment.1⟩, ?_⟩
  rfl

/-- Actual raw execution with a fixed loader root, terminal payload and all
pointwise admitted infinite runs. No implicit fairness filter is imposed. -/
def system {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (realization : WriteFile.Realization)
    (environment : ConsoleEnvironment) (interpretation : WriteFile.ReturnInterpretation)
    (covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)) : Grass.RelationalSystem (ULift.{1} Event) where
  State := ULift.{1} RawState
  Choice := Choice
  Graph := ULift.{1} Graph
  Initial := fun state graph => state.down = initialState loaded covered ∧ graph.down = []
  Step := fun graph before choice event after nextGraph =>
    RawStep loaded realization environment interpretation graph.down before.down choice event.down after.down nextGraph.down
  Terminal := fun state _ => ∃ call status, state.down.control = .terminal call status
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun before after => Graph.Extends before.down after.down
  extendsRefl := fun graph => Graph.extends_refl graph.down
  extendsTrans := Graph.extends_trans
  stepExtends := fun step => step.agreement.extendsGraph

/-- Project the recorded terminal payload. Registers and archived pending
tables are not used to guess an exit result. -/
def result (state : RawState) : Option (CallProtocol.CallId × BitVec 32) :=
  match state.control with
  | .terminal call status => some (call, status)
  | .caller _ | .pending _ _ _ => none

theorem terminal_result {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (realization : WriteFile.Realization)
    (environment : ConsoleEnvironment) (interpretation : WriteFile.ReturnInterpretation)
    (covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag))
    (state : ULift.{1} RawState) (graph : ULift.{1} Graph) :
    (system loaded realization environment interpretation covered).Terminal state graph ↔
      ∃ outcome, result state.down = some outcome := by
  cases control : state.down.control <;> simp [system, result, control]

/-- The terminal predicate forbids every actual next step, including service
and return edges whose archival bookkeeping remains present. -/
theorem terminal_no_step {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)}
    {state : ULift.{1} RawState} {graph : ULift.{1} Graph}
    (terminal : (system loaded realization environment interpretation covered).Terminal state graph)
    (choice : Choice) (event : ULift.{1} Event) (next : ULift.{1} RawState) (nextGraph : ULift.{1} Graph) :
    ¬ (system loaded realization environment interpretation covered).Step
      graph state choice event next nextGraph := by
  obtain ⟨call, status, terminal⟩ := terminal
  exact RawStep.terminal_no_step terminal

/-- Every admitted prefix retains the computed loader/protocol root. This
does not supply the missing raw edges from that root to a chosen endpoint. -/
theorem prefix_initial {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)}
    (execution : (system loaded realization environment interpretation covered).ExecutionPrefix) :
    execution.initialState.down = initialState loaded covered ∧ execution.initialGraph.down = [] :=
  execution.runs.initialValid

/-- Every infinite stream of actual edges from this exact reached frontier is
admitted. No fairness, provider responsiveness or silent-loop exclusion is added. -/
theorem infinite_admitted {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)}
    (execution : (system loaded realization environment interpretation covered).ExecutionPrefix)
    (states : Nat → RawState) (graphs : Nat → Graph) (choices : Nat → Choice) (events : Nat → Event)
    (stateZero : states 0 = execution.state.down) (graphZero : graphs 0 = execution.graph.down)
    (steps : ∀ index, RawStep loaded realization environment interpretation
      (graphs index) (states index) (choices index) (events index)
      (states (index + 1)) (graphs (index + 1))) :
    Nonempty ((system loaded realization environment interpretation covered).InfiniteContinuation
      execution.state execution.graph execution.events) := by
  exact ⟨{ stateAt := fun index => ⟨states index⟩
           graphAt := fun index => ⟨graphs index⟩
           choiceAt := choices
           eventAt := fun index => ⟨events index⟩
           stateZero := congrArg ULift.up stateZero
           graphZero := congrArg ULift.up graphZero
           step := steps
           consistent := trivial }⟩

end Grass.Platform.Win32.Raw
