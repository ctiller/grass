import Grass.Semantics.Execution

/-!
# Choice-bearing finite histories

`Path` stores every transition's state, graph, choice, and event as data.
Erasure recovers the existing proof-valued `Steps`/`Runs` interfaces, without
claiming those interfaces retain choices. Restriction returns both pieces and
an equation reconstructing the original path. No observation-stream law is
inferred from finite event traces.
-/

namespace Grass.RelationalSystem

universe u
variable {Event : Type u} {system : RelationalSystem Event}

/-- A finite path with its actual choices and intermediate configurations. -/
inductive Path (system : RelationalSystem Event) (start : system.State)
    (startGraph : system.Graph) : system.State → system.Graph → Type u where
  | nil : Path system start startGraph start startGraph
  | snoc {state graph} (prior : Path system start startGraph state graph)
      (choice : system.Choice) (event : Event) (next : system.State)
      (nextGraph : system.Graph)
      (valid : system.Step graph state choice event next nextGraph) :
      Path system start startGraph next nextGraph

namespace Path

variable {start middle finish : system.State} {sg mg fg : system.Graph}

/-- The exact finite audit events, before any observation projection. -/
def events {finish : system.State} {fg : system.Graph} : system.Path start sg finish fg → List Event
  | .nil => []
  | .snoc prior _ event _ _ _ => prior.events ++ [event]

/-- Choices remain data even when two transitions emit the same event. -/
def choices {finish : system.State} {fg : system.Graph} : system.Path start sg finish fg → List system.Choice
  | .nil => []
  | .snoc prior choice _ _ _ _ => prior.choices ++ [choice]

/-- Number of actual transitions. -/
def length {finish : system.State} {fg : system.Graph} : system.Path start sg finish fg → Nat
  | .nil => 0
  | .snoc prior _ _ _ _ _ => prior.length + 1

/-- Erase transition data to the old finite suffix relation. -/
theorem steps (path : system.Path start sg finish fg) :
    system.Steps start sg path.events finish fg := by
  induction path with
  | nil => exact .refl
  | snoc _ _ _ _ _ valid ih => exact .step ih valid

/-- Every actual finite path monotonically extends its initial graph. -/
theorem graphExtends (path : system.Path start sg finish fg) :
    system.Extends sg fg := path.steps.graphExtends

/-- Concatenate paths only at the same state and graph. -/
def append (first : system.Path start sg middle mg) {finish : system.State} {fg : system.Graph} :
    system.Path middle mg finish fg → system.Path start sg finish fg
  | .nil => first
  | .snoc prior choice event next nextGraph valid =>
      .snoc (first.append prior) choice event next nextGraph valid

@[simp] theorem append_nil (path : system.Path start sg finish fg) :
    path.append .nil = path := rfl

@[simp] theorem nil_append (path : system.Path start sg finish fg) :
    Path.nil.append path = path := by
  induction path with
  | nil => rfl
  | snoc _ _ _ _ _ _ ih => simp [append, ih]

theorem append_assoc {last : system.State} {lg : system.Graph}
    (first : system.Path start sg middle mg)
    (second : system.Path middle mg finish fg)
    (third : system.Path finish fg last lg) :
    (first.append second).append third = first.append (second.append third) := by
  induction third with
  | nil => rfl
  | snoc _ _ _ _ _ _ ih => simp [append, ih]

@[simp] theorem events_append (first : system.Path start sg middle mg)
    (second : system.Path middle mg finish fg) :
    (first.append second).events = first.events ++ second.events := by
  induction second with
  | nil => simp [append, events]
  | snoc _ _ _ _ _ _ ih => simp [append, events, ih, List.append_assoc]

@[simp] theorem choices_append (first : system.Path start sg middle mg)
    (second : system.Path middle mg finish fg) :
    (first.append second).choices = first.choices ++ second.choices := by
  induction second with
  | nil => simp [append, choices]
  | snoc _ _ _ _ _ _ ih => simp [append, choices, ih, List.append_assoc]

@[simp] theorem length_append (first : system.Path start sg middle mg)
    (second : system.Path middle mg finish fg) :
    (first.append second).length = first.length + second.length := by
  induction second with
  | nil => simp [append, length]
  | snoc _ _ _ _ _ _ ih => simp [append, length, ih, Nat.add_assoc]

@[simp] theorem events_length (path : system.Path start sg finish fg) :
    path.events.length = path.length := by
  induction path with
  | nil => rfl
  | snoc _ _ _ _ _ _ ih => simp [events, length, ih]

@[simp] theorem choices_length (path : system.Path start sg finish fg) :
    path.choices.length = path.length := by
  induction path with
  | nil => rfl
  | snoc _ _ _ _ _ _ ih => simp [choices, length, ih]

/-- A restriction retains a suffix reconstructing the exact original data. -/
structure Cut (path : system.Path start sg finish fg) (count : Nat) where
  state : system.State
  graph : system.Graph
  before : system.Path start sg state graph
  after : system.Path state graph finish fg
  reconstruct : before.append after = path
  beforeLength : before.length = min count path.length

/-- Restrict to the first `count` transitions, saturating at the full path. -/
def cut {finish : system.State} {fg : system.Graph}
    (path : system.Path start sg finish fg) (count : Nat) : path.Cut count :=
  match path with
  | .nil => ⟨_, _, .nil, .nil, rfl, by simp [length]⟩
  | .snoc prior choice event next nextGraph valid => by
      by_cases within : count ≤ prior.length
      · let split := prior.cut count
        refine ⟨split.state, split.graph, split.before,
          .snoc split.after choice event next nextGraph valid, ?_, ?_⟩
        · simp only [append, split.reconstruct]
        · rw [split.beforeLength]
          simp only [length]
          omega
      · exact ⟨next, nextGraph, .snoc prior choice event next nextGraph valid,
          .nil, rfl, by simp only [length]; omega⟩

/-- Restriction retains exactly the corresponding event prefix. -/
theorem Cut.events_take {path : system.Path start sg finish fg} {count : Nat}
    (split : path.Cut count) : split.before.events = path.events.take count := by
  have joined := congrArg Path.events split.reconstruct
  rw [events_append] at joined
  have len := split.beforeLength
  rw [← events_length] at len
  rw [← joined, List.take_append]
  by_cases h : count ≤ path.length
  · have eq : split.before.events.length = count := by omega
    simp only [← eq, List.take_length, Nat.sub_self, List.take_zero, List.append_nil]
  · have eq : split.before.events.length = path.length := by omega
    have empty : split.after.events = [] := by
      have sizes := congrArg List.length joined
      simp only [List.length_append, events_length] at sizes
      have plen := split.beforeLength
      have slen : split.after.events.length = 0 := by rw [events_length]; omega
      exact List.eq_nil_of_length_eq_zero slen
    simp [empty, List.take_of_length_le (by omega : split.before.events.length ≤ count)]

/-- Restriction retains the exact choice prefix, not just its length. -/
theorem Cut.choices_take {path : system.Path start sg finish fg} {count : Nat}
    (split : path.Cut count) : split.before.choices = path.choices.take count := by
  have joined := congrArg Path.choices split.reconstruct
  rw [choices_append] at joined
  have len := split.beforeLength
  rw [← choices_length] at len
  rw [← joined, List.take_append]
  by_cases h : count ≤ path.length
  · have eq : split.before.choices.length = count := by omega
    simp only [← eq, List.take_length, Nat.sub_self, List.take_zero, List.append_nil]
  · have eq : split.before.choices.length = path.length := by omega
    have empty : split.after.choices = [] := by
      have sizes := congrArg List.length joined
      simp only [List.length_append, choices_length] at sizes
      have plen := split.beforeLength
      have slen : split.after.choices.length = 0 := by rw [choices_length]; omega
      exact List.eq_nil_of_length_eq_zero slen
    simp [empty, List.take_of_length_le (by omega : split.before.choices.length ≤ count)]

end Path

/-- Every old finite suffix has a choice-bearing witness; the existential does
not select a canonical choice or identify different witnesses. -/
theorem Steps.hasPath {start finish : system.State} {sg fg : system.Graph}
    {events : List Event} (steps : system.Steps start sg events finish fg) :
    ∃ path : system.Path start sg finish fg, path.events = events := by
  induction steps with
  | refl => exact ⟨.nil, rfl⟩
  | @step events current currentGraph choice event next nextGraph _ valid ih =>
      obtain ⟨prior, same⟩ := ih
      exact ⟨.snoc prior choice event next nextGraph valid, by simp [Path.events, same]⟩

/-- An initialized finite history whose transition choices are retained as data. -/
structure History (system : RelationalSystem Event) where
  initialState : system.State
  initialGraph : system.Graph
  state : system.State
  graph : system.Graph
  validInitial : system.Initial initialState initialGraph
  path : system.Path initialState initialGraph state graph

namespace History

/-- Package a zero-step history at any valid initial configuration. -/
def initial {state : system.State} {graph : system.Graph}
    (valid : system.Initial state graph) : system.History :=
  ⟨state, graph, state, graph, valid, .nil⟩

/-- Forget choices and intermediate configurations, preserving the old API. -/
def erase (history : system.History) : system.ExecutionPrefix where
  initialState := history.initialState
  initialGraph := history.initialGraph
  state := history.state
  graph := history.graph
  events := history.path.events
  runs := Runs.ofInitialSteps history.validInitial history.path.steps

/-- Extend an initialized history by a coherent suffix. -/
def append (history : system.History) {state : system.State} {graph : system.Graph}
    (suffix : system.Path history.state history.graph state graph) : system.History :=
  ⟨history.initialState, history.initialGraph, state, graph, history.validInitial,
    history.path.append suffix⟩

/-- History append erases to the existing prefix append operation. -/
theorem erase_append (history : system.History)
    {state : system.State} {graph : system.Graph}
    (suffix : system.Path history.state history.graph state graph) :
    (history.append suffix).erase = history.erase.append suffix.steps := by
  apply ExecutionPrefix.ext <;> simp [erase, append, ExecutionPrefix.append]

/-- Every old packaged prefix is the erasure of an actual history. -/
theorem erase_surjective : Function.Surjective (erase (system := system)) := by
  intro execution
  obtain ⟨path, same⟩ := execution.runs.steps.hasPath
  refine ⟨⟨execution.initialState, execution.initialGraph, execution.state,
    execution.graph, execution.runs.initialValid, path⟩, ?_⟩
  apply ExecutionPrefix.ext <;> first | rfl | exact same

/-- Retain the first `count` transitions and the exact original initial state. -/
def restrict (history : system.History) (count : Nat) : system.History :=
  let split := history.path.cut count
  ⟨history.initialState, history.initialGraph, split.state, split.graph,
    history.validInitial, split.before⟩

/-- Restriction erases to the original event trace's prefix. -/
theorem restrict_events (history : system.History) (count : Nat) :
    (history.restrict count).erase.events = history.erase.events.take count :=
  (history.path.cut count).events_take

/-- The restricted history and retained suffix reconstruct the original
history, including its actual transition choices and configurations. -/
theorem restrict_append (history : system.History) (count : Nat) :
    (history.restrict count).append (history.path.cut count).after = history := by
  cases history with
  | mk initialState initialGraph state graph validInitial path =>
      change History.mk initialState initialGraph state graph validInitial
        ((path.cut count).before.append (path.cut count).after) = _
      rw [(path.cut count).reconstruct]

/-- Restriction retains exactly the selected number of actual choices. -/
theorem restrict_length (history : system.History) (count : Nat) :
    (history.restrict count).path.length = min count history.path.length :=
  (history.path.cut count).beforeLength

/-- The choices in a restricted history are exactly the original choice prefix. -/
theorem restrict_choices (history : system.History) (count : Nat) :
    (history.restrict count).path.choices = history.path.choices.take count :=
  (history.path.cut count).choices_take

end History
end Grass.RelationalSystem
