import Grass.CFG.Graph

/-!
# Structural CFG join discovery

`Graph.discoverJoins` derives shared targets from the graph's nested edge lists.
`JoinSelection.wellFormed` accepts only the exact discovered identity list in
canonical order, selecting contracts already stored in the graph rather than
supplying a second contract value.  `JoinDemand.cyclic` reports cycle
participation as structural data for the later loop checker; this module does
not choose loop headers or invent loop invariants.
-/

namespace Grass.CFG

universe u v

namespace Graph

variable {State : Type u} {Terminal : Type v}

/-- Direct successor identities of one block, retaining outgoing-edge order. -/
def successorIds (graph : Graph State Terminal) (source : BlockId) : List BlockId :=
  match graph.findBlock? source with
  | none => []
  | some block => block.outgoing.filterMap fun edge =>
      match edge.target with
      | .block id => some id
      | .terminal _ => none

/-- Fuel sufficient for the finite worklist used by `Graph.reachable`. -/
def traversalFuel (graph : Graph State Terminal) : Nat :=
  graph.blocks.length +
    2 * graph.blocks.foldl (fun total block => total + block.outgoing.length) 0 + 1

private def reachableAux (graph : Graph State Terminal) (target : BlockId) :
    Nat → List BlockId → List BlockId → Bool
  | 0, _, _ => false
  | _ + 1, [], _ => false
  | fuel + 1, current :: rest, visited =>
      if current == target then
        true
      else if visited.contains current then
        reachableAux graph target fuel rest visited
      else
        reachableAux graph target fuel
          (rest ++ graph.successorIds current) (current :: visited)

/-- Whether a nonempty direct-edge path leads from `source` to `target`. -/
def reachable (graph : Graph State Terminal) (source target : BlockId) : Bool :=
  reachableAux graph target graph.traversalFuel (graph.successorIds source) []

/-- Whether a block participates in a directed cycle. -/
def cyclicAt (graph : Graph State Terminal) (id : BlockId) : Bool :=
  graph.reachable id id

/-- Structurally discovered information for one shared target. -/
structure JoinDemand where
  id : BlockId
  predecessors : List BlockId
  cyclic : Bool
deriving Repr, DecidableEq

/-- Shared targets in block order.  Ordinary single-predecessor targets are
absent and may inherit their incoming postcondition during block checking. -/
def discoverJoins (graph : Graph State Terminal) : List JoinDemand :=
  graph.blocks.filterMap fun block =>
    let predecessors := graph.predecessors block.id
    if 2 ≤ predecessors.length then
      some ⟨block.id, predecessors, graph.cyclicAt block.id⟩
    else
      none

/-- The exact identities demanded by structural join discovery. -/
def discoveredJoinIds (graph : Graph State Terminal) : List BlockId :=
  graph.discoverJoins.map JoinDemand.id

/-- `Graph.mem_blockIds_of_mem_discoveredJoinIds` states that every discovered
join identity names a block structurally present in the authored CFG, even
before graph well-formedness is established. -/
theorem mem_blockIds_of_mem_discoveredJoinIds
    (graph : Graph State Terminal) (id : BlockId)
    (member : id ∈ graph.discoveredJoinIds) :
    id ∈ graph.blockIds := by
  rcases List.mem_map.mp member with ⟨demand, demandMember, rfl⟩
  rw [discoverJoins, List.mem_filterMap] at demandMember
  rcases demandMember with ⟨block, blockMember, selected⟩
  apply List.mem_map.mpr
  refine ⟨block, blockMember, ?_⟩
  dsimp only at selected
  split at selected
  · cases selected
    rfl
  · contradiction

end Graph

/-- Join-contract selection by identity.  Each identity denotes the contract
already stored in the graph, avoiding a second value that could disagree with
the block being selected. -/
structure JoinSelection (State : Type u) (Terminal : Type v) where
  graph : Graph State Terminal
  selected : List BlockId

namespace JoinSelection

variable {State : Type u} {Terminal : Type v}

/-- Selected identities in authored order. -/
def selectedIds (selection : JoinSelection State Terminal) : List BlockId :=
  selection.selected

/-- Executable closure check for a join selection. -/
def wellFormed (selection : JoinSelection State Terminal) : Bool :=
  selection.graph.wellFormed &&
  decide (selection.selectedIds = selection.graph.discoveredJoinIds)

/-- Certificate-facing statement of exact join selection. -/
def WellFormed (selection : JoinSelection State Terminal) : Prop :=
  selection.wellFormed = true

instance (selection : JoinSelection State Terminal) : Decidable selection.WellFormed :=
  inferInstanceAs (Decidable (selection.wellFormed = true))

/-- Public decomposition of the executable join-selection checker. -/
@[simp] theorem wellFormed_iff (selection : JoinSelection State Terminal) :
    selection.WellFormed ↔
      selection.graph.WellFormed ∧
        selection.selectedIds = selection.graph.discoveredJoinIds := by
  simp [WellFormed, wellFormed, Graph.WellFormed]

/-- A valid join selection carries a structurally well-formed source graph. -/
theorem graphWellFormed_of_wellFormed
    (selection : JoinSelection State Terminal) (closed : selection.WellFormed) :
    selection.graph.WellFormed :=
  (selection.wellFormed_iff.mp closed).1

/-- A valid join selection is exactly structural discovery, including its
canonical block order. -/
theorem selectedIds_eq_discoveredJoinIds_of_wellFormed
    (selection : JoinSelection State Terminal) (closed : selection.WellFormed) :
    selection.selectedIds = selection.graph.discoveredJoinIds :=
  (selection.wellFormed_iff.mp closed).2

/-- Every identity accepted by a valid join selection names an authored block. -/
theorem mem_blockIds_of_mem_selected
    (selection : JoinSelection State Terminal) (closed : selection.WellFormed)
    (id : BlockId) (member : id ∈ selection.selectedIds) :
    id ∈ selection.graph.blockIds := by
  rw [selection.selectedIds_eq_discoveredJoinIds_of_wellFormed closed] at member
  exact selection.graph.mem_blockIds_of_mem_discoveredJoinIds id member

end JoinSelection

end Grass.CFG
