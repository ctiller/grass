import Grass.Semantics.Waiting

/-!
# Timing strategies for an isolated wait boundary

This deliberately narrow interface retains every relational history, terminal
completion, and infinite continuation.  A strategy controls only whether an
already protocol-permitted permanent nonresponse is compatible.  It is not the
general scheduling strategy interface described for concurrent specifications.

Terminal-status observation is a later provider/projection obligation; a
terminal state alone does not establish that external observation bridge.
-/

namespace Grass.RelationalSystem

universe u

variable {Event Request : Type u} {system : RelationalSystem Event}
  {protocol : WaitProtocol Request} {boundary : system.WaitBoundary protocol}

/-- The only selectable timing fact is permanent nonresponse at an exact wait. -/
structure BoundaryTimingStrategy (boundary : system.WaitBoundary protocol) where
  permitsNonresponse : ∀ history, PermanentWait boundary history → Prop

namespace BoundaryTimingStrategy

/-- A strategy under which every pending external interaction must answer. -/
def responding (boundary : system.WaitBoundary protocol) : BoundaryTimingStrategy boundary where
  permitsNonresponse := fun _ _ => False

/-- The unrestricted timing strategy retains every protocol-permitted wait. -/
def unrestricted (boundary : system.WaitBoundary protocol) : BoundaryTimingStrategy boundary where
  permitsNonresponse := fun _ _ => True

/-- `BoundaryTimingStrategy.Compatible` admits terminal results and infinite
transition paths unconditionally. -/
def Compatible (strategy : BoundaryTimingStrategy boundary) :
    CompleteHistory boundary → Prop
  | .terminal _ _ => True
  | .infinite _ _ => True
  | .waiting history wait => strategy.permitsNonresponse history wait

/-- A generated maximal behavior is an existing complete history plus only its
selected nonresponse timing evidence. -/
def GeneratedComplete (strategy : BoundaryTimingStrategy boundary) :=
  {complete : CompleteHistory boundary // strategy.Compatible complete}

/-- Every terminal completion is retained by every boundary timing strategy. -/
def terminalCompatible (strategy : BoundaryTimingStrategy boundary)
    (history : system.History) (finished : system.Terminal history.state history.graph) :
    strategy.GeneratedComplete :=
  ⟨.terminal history finished, trivial⟩

/-- Every infinite transition sequence is retained by every boundary timing strategy. -/
def infiniteCompatible (strategy : BoundaryTimingStrategy boundary)
    (history : system.History)
    (continuation : system.InfiniteContinuation history.state history.graph history.path.events) :
    strategy.GeneratedComplete :=
  ⟨.infinite history continuation, trivial⟩

end BoundaryTimingStrategy

/-- Fixed responsiveness for this isolated boundary: no permanent nonresponse
selected by the timing strategy. Infinite sequences of actual replies remain allowed. -/
def BoundaryResponsive (strategy : BoundaryTimingStrategy boundary) : Prop :=
  ∀ _history wait, ¬ strategy.permitsNonresponse _history wait

/-- A concrete terminal suffix from one exact reachable history. -/
structure TerminalExtension (boundary : system.WaitBoundary protocol)
    (history : system.History) where
  state : system.State
  graph : system.Graph
  path : system.Path history.state history.graph state graph
  finished : system.Terminal state graph

/-- Terminal completion from every finite history is an explicit system law,
rather than an automatic claim about arbitrary relational systems. -/
structure BoundaryTerminalAdequate (boundary : system.WaitBoundary protocol) : Prop where
  complete : ∀ history : system.History, Nonempty (TerminalExtension boundary history)

/-- Every allowed dependent response supplies the exact appended history. All
finite histories are retained because the timing strategy has no history filter. -/
theorem allowedReplyHistory (history : system.History) (occurrence : boundary.Occurrence)
    (pending : boundary.Pending history occurrence)
    (response : protocol.Response (boundary.request occurrence))
    (allowed : protocol.Allowed (boundary.request occurrence) response) :
    ∃ choice event next nextGraph,
      boundary.Reply occurrence response choice ∧
      ∃ transition : system.Step history.graph history.state choice event next nextGraph,
        (history.append (.snoc .nil choice event next nextGraph transition)).state = next := by
  obtain ⟨choice, event, next, nextGraph, reply, transition⟩ :=
    boundary.reply_step history occurrence pending response allowed
  exact ⟨choice, event, next, nextGraph, reply, transition, rfl⟩

@[simp] theorem responding_responsive (boundary : system.WaitBoundary protocol) :
    BoundaryResponsive (BoundaryTimingStrategy.responding boundary) := by
  intro history wait
  simp [BoundaryTimingStrategy.responding]

end Grass.RelationalSystem
