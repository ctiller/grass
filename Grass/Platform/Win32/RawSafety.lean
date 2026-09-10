import Grass.Platform.Win32.RawPrefix
import Grass.Platform.Win32.RawPhasePreservation
import Grass.Semantics.History

/-! Safety coverage for the installed raw relation.

The predicate here ranges over every initialized, choice-bearing finite history
of the fixed raw system.  It rules out only the explicit `outsideProfile`
diagnostic event; it does not state memory safety, deadlock freedom, native
adequacy, or that an edge is enabled. -/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
  {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
    (FreshSupply.initial : FreshSupply GrantTag)}

/-- An exact raw audit event is covered when it is not an explicit checked or
CPU outside-profile diagnostic. -/
def EventCovered (event : ULift.{1} Event) : Prop :=
  ∀ reason, event.down.kind ≠ .outsideProfile reason

/-- Every event in every actual initialized raw history is covered. This is a
finite execution-coverage predicate only; it makes no claim about complete
memory safety or deadlock freedom. -/
def Coverage : Prop :=
  ∀ history : (system loaded realization environment interpretation covered).History,
    ∀ event ∈ history.path.events, EventCovered event

/-- Every actual one-step extension from an already initialized raw history is
covered. The history retains its original choices; no canonical execution is
selected. -/
def OutgoingCoverage : Prop :=
  ∀ (history : (system loaded realization environment interpretation covered).History)
    {next : ULift.{1} RawState} {nextGraph : ULift.{1} Graph}
    (choice : Choice) (event : ULift.{1} Event)
    (_step : (system loaded realization environment interpretation covered).Step
      history.graph history.state choice event next nextGraph),
    EventCovered event

/-- Coverage excludes an outside-profile event at each actual outgoing edge.
The one-step path is appended to the supplied history, so the proof applies to
the exact reached state, graph, and original preceding choices. -/
theorem Coverage.outgoing {coverage : Coverage (loaded := loaded) (realization := realization)
    (environment := environment) (interpretation := interpretation) (covered := covered)}
    (history : (system loaded realization environment interpretation covered).History)
    {next : ULift.{1} RawState} {nextGraph : ULift.{1} Graph}
    (choice : Choice) (event : ULift.{1} Event)
    (step : (system loaded realization environment interpretation covered).Step
      history.graph history.state choice event next nextGraph) :
    EventCovered event := by
  have member : event ∈ (history.append (.snoc .nil choice event next nextGraph step)).path.events := by
    change event ∈ history.path.events ++ [event]
    simp
  exact coverage (history.append (.snoc .nil choice event next nextGraph step)) event member

/-- Checking every actual outgoing edge from every reached initialized history
suffices for `Coverage`. The induction is over the supplied path itself, and
therefore preserves the path's actual choices and intermediate configurations. -/
theorem coverage_of_outgoing
    (outgoing : OutgoingCoverage (loaded := loaded) (realization := realization)
      (environment := environment) (interpretation := interpretation) (covered := covered)) :
    Coverage (loaded := loaded) (realization := realization) (environment := environment)
      (interpretation := interpretation) (covered := covered) := by
  rintro ⟨initialState, initialGraph, state, graph, validInitial, path⟩ event member
  induction path with
  | nil => simp [Grass.RelationalSystem.Path.events] at member
  | @snoc state graph prior choice last next nextGraph step ih =>
      let priorHistory : (system loaded realization environment interpretation covered).History :=
        { initialState := initialState
          initialGraph := initialGraph
          state := state
          graph := graph
          validInitial := validInitial
          path := prior }
      have lastCovered := outgoing priorHistory choice last step
      simp only [Grass.RelationalSystem.Path.events, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · exact ih earlier
      · exact lastCovered

/-- The fixed all-history predicate and the reached-edge formulation are
equivalent. -/
theorem coverage_iff_outgoing :
    Coverage (loaded := loaded) (realization := realization) (environment := environment)
      (interpretation := interpretation) (covered := covered) ↔
    OutgoingCoverage (loaded := loaded) (realization := realization) (environment := environment)
      (interpretation := interpretation) (covered := covered) :=
  ⟨fun coverage => fun history {_next} {_nextGraph} choice event step =>
      Coverage.outgoing (coverage := coverage) history (choice := choice) (event := event) step,
    coverage_of_outgoing⟩

/-- Under `Coverage`, every actual raw CPU edge has the completed CPU event,
because `RawStep.cpu_event` leaves outside-profile as its only alternative. -/
theorem Coverage.cpu_completed {coverage : Coverage (loaded := loaded) (realization := realization)
    (environment := environment) (interpretation := interpretation) (covered := covered)}
    (history : (system loaded realization environment interpretation covered).History)
    {next : ULift.{1} RawState} {nextGraph : ULift.{1} Graph}
    {choice : Grass.ISA.X86.Execution.CheckedChoice} (event : ULift.{1} Event)
    (step : (system loaded realization environment interpretation covered).Step
      history.graph history.state (.cpu choice) event next nextGraph) :
    event.down.kind = .cpu .completed := by
  have rawStep : RawStep loaded realization environment interpretation
      history.graph.down history.state.down (.cpu choice) event.down next.down nextGraph.down := step
  rcases rawStep.cpu_event with completed | ⟨reason, outside⟩
  · exact completed
  · exact False.elim ((Coverage.outgoing (coverage := coverage) history
      (choice := .cpu choice) (event := event) step) reason outside)

end Grass.Platform.Win32.Raw
