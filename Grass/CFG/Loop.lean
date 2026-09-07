import Grass.CFG.Join

/-!
# Structural loop regions and explicit obligations

Loop regions are the nontrivial strongly connected components induced by the
graph's direct edges, including singleton self-loops.  Discovery chooses the
first member in graph order as a stable region identity; that representative is
not silently promoted into a semantic loop header.  Each discovered region must
receive an explicit invariant and either a ranking measure or frontier law.
-/

namespace Grass.CFG

universe u v

namespace Graph

variable {State : Type u} {Terminal : Type v}

/-- Members mutually reachable with `root`, in canonical block order. -/
def loopRegionMembers (graph : Graph State Terminal) (root : BlockId) : List BlockId :=
  graph.blocks.filterMap fun block =>
    if graph.reachable root block.id && graph.reachable block.id root then
      some block.id
    else
      none

/-- One structurally discovered cyclic region. -/
structure LoopDemand where
  representative : BlockId
  members : List BlockId
deriving Repr, DecidableEq

private def discoverLoopsAux (graph : Graph State Terminal) :
    List (Block State Terminal) → List BlockId → List LoopDemand
  | [], _ => []
  | block :: rest, covered =>
      if covered.contains block.id then
        discoverLoopsAux graph rest covered
      else if graph.cyclicAt block.id then
        let members := graph.loopRegionMembers block.id
        ⟨block.id, members⟩ :: discoverLoopsAux graph rest (covered ++ members)
      else
        discoverLoopsAux graph rest covered

/-- Cyclic strongly connected regions in canonical graph order. -/
def discoverLoops (graph : Graph State Terminal) : List LoopDemand :=
  discoverLoopsAux graph graph.blocks []

/-- Canonical identities of all discovered cyclic regions. -/
def discoveredLoopIds (graph : Graph State Terminal) : List BlockId :=
  graph.discoverLoops.map LoopDemand.representative

end Graph

/-- Explicit progress argument attached to a cyclic region.  The later block
checker proves that each admitted cycle step decreases the rank or advances the
frontier; merely constructing this value grants no such proof. -/
inductive LoopProgress (State : Type u) where
  | measure (rank : State → Nat)
  | frontier (advances : State → State → Prop)

/-- Authored logical obligation for one structurally discovered cyclic region. -/
structure LoopObligation (State : Type u) where
  region : BlockId
  invariant : State → Prop
  progress : LoopProgress State

/-- Raw loop-obligation selection over a graph. -/
structure LoopSelection {State : Type u} {Terminal : Type v}
    (graph : Graph State Terminal) where
  selected : List (LoopObligation State)

namespace LoopSelection

variable {State : Type u} {Terminal : Type v} {graph : Graph State Terminal}

/-- Selected cyclic-region identities in authored order. -/
def selectedIds (selection : LoopSelection graph) : List BlockId :=
  selection.selected.map LoopObligation.region

/-- Executable closure check requiring one obligation per discovered region. -/
def wellFormed (selection : LoopSelection graph) : Bool :=
  graph.wellFormed && decide (selection.selectedIds = graph.discoveredLoopIds)

/-- Certificate-facing statement for `LoopSelection.wellFormed`. -/
def WellFormed (selection : LoopSelection graph) : Prop :=
  selection.wellFormed = true

instance (selection : LoopSelection graph) : Decidable selection.WellFormed :=
  inferInstanceAs (Decidable (selection.wellFormed = true))

/-- Public decomposition of exact loop-obligation selection. -/
@[simp] theorem wellFormed_iff (selection : LoopSelection graph) :
    selection.WellFormed ↔
      graph.WellFormed ∧ selection.selectedIds = graph.discoveredLoopIds := by
  simp [WellFormed, wellFormed, Graph.WellFormed]

end LoopSelection

end Grass.CFG
