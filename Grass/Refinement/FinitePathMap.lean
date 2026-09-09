import Grass.Semantics.History

/-! Finite structural path mapping. A mapped lower transition may expand to
zero, one, or many upper transitions. No observation, terminal, divergence, or
liveness property is implied. -/

namespace Grass.RelationalSystem

universe u v w

structure PathMap {LowerEvent : Type u} {UpperEvent : Type v}
    (lower : RelationalSystem LowerEvent) (upper : RelationalSystem UpperEvent) where
  mapState : lower.State → upper.State
  mapGraph : lower.Graph → upper.Graph
  mapInitial : ∀ {state graph}, lower.Initial state graph →
    upper.Initial (mapState state) (mapGraph graph)
  mapStep : ∀ {graph state choice event next nextGraph},
    lower.Step graph state choice event next nextGraph →
      upper.Path (mapState state) (mapGraph graph) (mapState next) (mapGraph nextGraph)

namespace PathMap

variable {LowerEvent : Type u} {UpperEvent : Type v}
variable {lower : RelationalSystem LowerEvent} {upper : RelationalSystem UpperEvent}

/-- Fold the actual lower path, concatenating the finite upper path supplied for
each stored transition proof. -/
def mapPath (mapping : PathMap lower upper) {start finish : lower.State}
    {startGraph finishGraph : lower.Graph} :
    lower.Path start startGraph finish finishGraph →
      upper.Path (mapping.mapState start) (mapping.mapGraph startGraph)
        (mapping.mapState finish) (mapping.mapGraph finishGraph)
  | .nil => .nil
  | .snoc prior _choice _event next nextGraph valid =>
      (mapping.mapPath prior).append (mapping.mapStep valid)

@[simp] theorem mapPath_nil (mapping : PathMap lower upper)
    {state : lower.State} {graph : lower.Graph} :
    mapping.mapPath (Path.nil : lower.Path state graph state graph) = .nil := rfl

/-- Mapping commutes with concatenation of concrete finite paths. -/
theorem mapPath_append (mapping : PathMap lower upper)
    {start middle finish : lower.State} {startGraph middleGraph finishGraph : lower.Graph}
    (first : lower.Path start startGraph middle middleGraph)
    (second : lower.Path middle middleGraph finish finishGraph) :
    mapping.mapPath (first.append second) =
      (mapping.mapPath first).append (mapping.mapPath second) := by
  induction second with
  | nil => rfl
  | snoc prior choice event next nextGraph valid ih =>
      simp only [Path.append, mapPath, ih, Path.append_assoc]

/-- Map the exact initial configuration and the complete stored finite path. -/
def mapHistory (mapping : PathMap lower upper) (history : lower.History) : upper.History :=
  ⟨mapping.mapState history.initialState, mapping.mapGraph history.initialGraph,
    mapping.mapState history.state, mapping.mapGraph history.graph,
    mapping.mapInitial history.validInitial, mapping.mapPath history.path⟩

@[simp] theorem mapHistory_initialState (mapping : PathMap lower upper)
    (history : lower.History) :
    (mapping.mapHistory history).initialState = mapping.mapState history.initialState := rfl

@[simp] theorem mapHistory_initialGraph (mapping : PathMap lower upper)
    (history : lower.History) :
    (mapping.mapHistory history).initialGraph = mapping.mapGraph history.initialGraph := rfl

@[simp] theorem mapHistory_state (mapping : PathMap lower upper) (history : lower.History) :
    (mapping.mapHistory history).state = mapping.mapState history.state := rfl

@[simp] theorem mapHistory_graph (mapping : PathMap lower upper) (history : lower.History) :
    (mapping.mapHistory history).graph = mapping.mapGraph history.graph := rfl

/-- Mapping a history extension equals extending the mapped history by the
mapped suffix. -/
theorem mapHistory_append (mapping : PathMap lower upper) (history : lower.History)
    {state : lower.State} {graph : lower.Graph}
    (suffix : lower.Path history.state history.graph state graph) :
    mapping.mapHistory (history.append suffix) =
      (mapping.mapHistory history).append (mapping.mapPath suffix) := by
  cases history with
  | mk initialState initialGraph current currentGraph validInitial path =>
      simp only [History.append, mapHistory]
      rw [mapPath_append]

/-- A mapped restricted history and its mapped retained suffix reconstruct the
mapped whole history exactly. -/
theorem mapHistory_restrict_append (mapping : PathMap lower upper)
    (history : lower.History) (count : Nat) :
    (mapping.mapHistory (history.restrict count)).append
        (mapping.mapPath (history.path.cut count).after) =
      mapping.mapHistory history := by
  rw [← mapping.mapHistory_append (history.restrict count) (history.path.cut count).after,
    history.restrict_append]

/-- Compose the supplied finite transition paths through an intermediate system. -/
def trans {MiddleEvent : Type w} {middle : RelationalSystem MiddleEvent}
    (first : PathMap lower middle) (second : PathMap middle upper) : PathMap lower upper where
  mapState := fun state => second.mapState (first.mapState state)
  mapGraph := fun graph => second.mapGraph (first.mapGraph graph)
  mapInitial := fun valid => second.mapInitial (first.mapInitial valid)
  mapStep := fun valid => second.mapPath (first.mapStep valid)

/-- `mapPath_trans` preserves the exact intermediate path, including its choices. -/
theorem mapPath_trans {MiddleEvent : Type w} {middle : RelationalSystem MiddleEvent}
    (first : PathMap lower middle) (second : PathMap middle upper)
    {start finish : lower.State} {startGraph finishGraph : lower.Graph}
    (path : lower.Path start startGraph finish finishGraph) :
    (first.trans second).mapPath path = second.mapPath (first.mapPath path) := by
  induction path with
  | nil => rfl
  | snoc prior choice event next nextGraph valid ih =>
      simp only [mapPath, second.mapPath_append]
      rw [ih]
      rfl

/-- The complete finite history maps through the same intermediate witness. -/
theorem mapHistory_trans {MiddleEvent : Type w} {middle : RelationalSystem MiddleEvent}
    (first : PathMap lower middle) (second : PathMap middle upper) (history : lower.History) :
    (first.trans second).mapHistory history = second.mapHistory (first.mapHistory history) := by
  cases history with
  | mk initialState initialGraph state graph validInitial path =>
      simp only [mapHistory]
      rw [mapPath_trans]
      rfl

end PathMap
end Grass.RelationalSystem
