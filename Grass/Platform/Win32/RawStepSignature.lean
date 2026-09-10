import Grass.Platform.Win32.RawState
import Grass.Platform.Win32.WriteFileReturn
import Grass.ISA.X86.Execution.CheckedChoice
import Grass.ISA.X86.Execution.RawOutcome
import Grass.ISA.X86.Execution.CallFactory
import Grass.ISA.X86.Execution.ReturnSlotFactory
import Grass.ISA.X86.Execution.ComputationFactory
import Grass.ISA.X86.Execution.PushFactory
import Grass.ISA.X86.Execution.CheckedStep

/-!
# Fixed Windows raw-step interface

These are shared data and signature definitions, not an implemented transition
relation. No constructor here licenses a provider action, observation, fault,
or terminal result. Fixed CPU and endpoint definitions must justify each edge.
In particular, `StepSignature` is a type, not an empty or unconstrained model.
-/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86.Execution
open Grass.Platform.Win32.ExecutionState

/-- Explicit choices retained by a raw history. Policy/action values describe
the choice; only the fixed transition relation may establish its admissibility. -/
inductive Choice where
  | cpu (choice : CheckedChoice)
  | apiEntry (request : ApiRequest) (agent : ContextId)
  | providerService (call : CallProtocol.CallId) (agent : ContextId)
      (action : WriteFile.Action)
  | providerReturn (call : CallProtocol.CallId) (result : WriteFile.ReturnResult)
      (gpr : Grass.ISA.X86.Gpr → BitVec 64) (rflags : BitVec 64)
  | stdoutResult (call : CallProtocol.CallId)
      (gpr : Grass.ISA.X86.Gpr → BitVec 64) (rflags : BitVec 64)
  | exitObservation (call : CallProtocol.CallId) (status : BitVec 32)

/-- Endpoint observation data. Actual endpoint receipts must derive these
values; they are not themselves evidence of publication, return or process exit. -/
inductive Observation where
  | stdoutAcquired (call : CallProtocol.CallId) (handle : BitVec 64)
  | published (call : CallProtocol.CallId) (bytes : Vec Byte)
  | apiReturned (call : CallProtocol.CallId) (result : WriteFile.ReturnResult)
  | processExited (call : CallProtocol.CallId) (status : BitVec 32)

/-- A reached applicability diagnostic does not assert a physical outcome. -/
inductive Failure where
  | checked (reason : CheckedExecution.Failure)
  | cpu (reason : ApplicabilityFailure)
  | fetch (reason : FetchFactory.Failure)
  | computation (reason : ComputationFactory.Failure)
  | push (reason : PushFactory.Failure)
  | call (reason : CallFactory.Failure)
  | returnSlot (reason : ReturnSlotFactory.Failure)
  | protocolCheck

/-- Internal and CPU steps stay distinguishable from endpoint observations and
uncovered prefixes. In particular, a silent CPU loop is not provider waiting. -/
inductive EventKind where
  | internal
  | cpu (event : CpuEvent)
  | endpoint (observation : Observation)
  | outsideProfile (reason : Failure)

/-- Exactly the suffix contributed by one raw edge, not another cumulative log. -/
structure Event where
  memory : List ValidMemoryEvent
  boundaries : List CallProtocol.Boundary
  kind : EventKind

/-- Agreement with both canonical logs is a mandatory edge obligation. -/
def Event.Appends (event : Event) (before after : RawState) : Prop :=
  after.machine.machine.events = before.machine.machine.events ++ event.memory ∧
    after.metadata.boundaries = before.metadata.boundaries ++ event.boundaries

/-- Compute suffix data from the canonical logs. This does not assert that the
earlier logs are prefixes; `between_appends` requires that separate evidence. -/
def Event.between (before after : RawState) (kind : EventKind) : Event :=
  ⟨after.machine.machine.events.drop before.machine.machine.events.length,
   after.metadata.boundaries.drop before.metadata.boundaries.length, kind⟩

/-- Exact append evidence makes the computed suffix the edge's actual logs. -/
theorem Event.between_appends {before after : RawState} {kind : EventKind}
    {memory : List ValidMemoryEvent} {boundaries : List CallProtocol.Boundary}
    (memoryExact : after.machine.machine.events = before.machine.machine.events ++ memory)
    (boundariesExact : after.metadata.boundaries = before.metadata.boundaries ++ boundaries) :
    (Event.between before after kind).Appends before after := by
  simp [Event.between, Event.Appends, memoryExact, boundariesExact]

/-- Append evidence determines both canonical event suffixes. -/
theorem Event.between_suffixes {before after : RawState} {kind : EventKind}
    {memory : List ValidMemoryEvent} {boundaries : List CallProtocol.Boundary}
    (memoryExact : after.machine.machine.events = before.machine.machine.events ++ memory)
    (boundariesExact : after.metadata.boundaries = before.metadata.boundaries ++ boundaries) :
    (Event.between before after kind).memory = memory ∧
      (Event.between before after kind).boundaries = boundaries := by
  simp [Event.between, memoryExact, boundariesExact]

/-- A graph node is represented only by an actual memory event or protocol
boundary in this raw state, even when its metadata does not currently pack. -/
def Represented (state : RawState) : WriteFile.CausalNode → Prop
  | .entry call => ∃ caller agent loans,
      CallProtocol.Boundary.handoff call caller agent loans ∈ state.metadata.boundaries
  | .returned call => ∃ caller agent loans,
      CallProtocol.Boundary.returned call caller agent loans ∈ state.metadata.boundaries
  | .event id => ∃ event ∈ state.machine.machine.events, event.event.id = id

/-- Only causal edges are stored; the machine and metadata own the event logs. -/
abbrev Graph := List (WriteFile.CausalNode × WriteFile.CausalNode)

/-- Every edge endpoint refers to the actual current logs. Acyclicity and
target-specific ordering remain additional fixed-model obligations. -/
def Graph.Endpoints (graph : Graph) (state : RawState) : Prop :=
  ∀ edge ∈ graph, Represented state edge.1 ∧ Represented state edge.2

/-- The finite causal graph has represented endpoints and no directed cycle.
This does not establish architecture-specific ordering requirements. -/
def Graph.WellFormed (graph : Graph) (state : RawState) : Prop :=
  graph.Endpoints state ∧
    ∀ node, ¬ Relation.TransGen (fun left right => (left, right) ∈ graph) node node

/-- Causal edges accumulate without dropping previous ordering evidence. -/
def Graph.Extends (before after : Graph) : Prop :=
  ∃ added, after = before ++ added

theorem Graph.extends_refl (graph : Graph) : graph.Extends graph :=
  ⟨[], (List.append_nil graph).symm⟩

theorem Graph.extends_trans {first middle last : Graph}
    (a : first.Extends middle) (b : middle.Extends last) : first.Extends last := by
  obtain ⟨left, rfl⟩ := a
  obtain ⟨right, rfl⟩ := b
  exact ⟨left ++ right, List.append_assoc _ _ _⟩

/-- The precise shape the fixed Windows transition definition must implement.
There is deliberately no value of this type installed as raw execution here. -/
abbrev StepSignature := Graph → RawState → Choice → Event → RawState → Graph → Prop

/-- Necessary log/graph agreement for an edge, not sufficient transition
evidence. It does not establish that any instruction or endpoint ran. -/
structure EdgeAgreement (graph : Graph) (before : RawState) (event : Event)
    (after : RawState) (nextGraph : Graph) : Prop where
  appends : event.Appends before after
  priorWellFormed : graph.WellFormed before
  nextWellFormed : nextGraph.WellFormed after
  extendsGraph : graph.Extends nextGraph

end Grass.Platform.Win32.Raw
