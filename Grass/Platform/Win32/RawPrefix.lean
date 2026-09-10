import Grass.Platform.Win32.RawStep
import Grass.Semantics.Execution

/-! Finite-prefix-only view of the fixed raw relation, reusing the existing
relational prefix carrier. The root is computed from the exact loaded machine
and fresh protocol supply. Terminal and infinite-consistency fields are unused
scaffolding, both False: this is NOT a complete raw behavior model. Do not use
these fields to claim absence of completion, deadlock, progress or termination.
Migrate this view to the canonical raw system when its completion semantics land.
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

/-- A finite-only instantiation, with actual raw steps and exact loader root.
The two False completion fields carry no claim about executable completion. -/
def finitePrefixSystem {image : ImageInput} {inputs : EntryInputs}
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
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => False
  Extends := fun before after => Graph.Extends before.down after.down
  extendsRefl := fun graph => Graph.extends_refl graph.down
  extendsTrans := Graph.extends_trans
  stepExtends := fun step => step.agreement.extendsGraph

/-- Every admitted prefix retains the computed loader/protocol root. This
does not supply the missing raw edges from that root to a chosen endpoint. -/
theorem finitePrefix_initial {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)}
    (execution : (finitePrefixSystem loaded realization environment interpretation covered).ExecutionPrefix) :
    execution.initialState.down = initialState loaded covered ∧ execution.initialGraph.down = [] :=
  execution.runs.initialValid

end Grass.Platform.Win32.Raw
