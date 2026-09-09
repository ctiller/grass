import Grass.CFG.Join

/-!
# Structural loop regions and explicit obligations

`Graph.loopRegionMembers` and `Graph.discoverLoops` compute cyclic regions from
mutual direct-edge reachability, including singleton self-loops. Discovery uses
the first member in graph order as the stable `LoopDemand.representative`; that
representative is not silently promoted into a semantic loop header.
`LoopSelection.wellFormed` requires one invariant and progress description at
each exact discovered identity. It is only structural selection: preservation,
rank decrease, and frontier advancement remain obligations for the later block
checker.
-/

namespace Grass.CFG

universe u v u₁ u₂

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
structure LoopSelection (State : Type u) (Terminal : Type v) where
  graph : Graph State Terminal
  selected : List (LoopObligation State)

namespace LoopSelection

variable {State : Type u} {Terminal : Type v}

/-- Selected cyclic-region identities in authored order. -/
def selectedIds (selection : LoopSelection State Terminal) : List BlockId :=
  selection.selected.map LoopObligation.region

/-- Find the first selected obligation for a discovered cyclic-region identity. -/
def findObligation? (selection : LoopSelection State Terminal) (region : BlockId) :
    Option (LoopObligation State) :=
  selection.selected.find? fun obligation => obligation.region == region

/-- A successful loop-obligation lookup returns an authored member carrying the
requested cyclic-region identity. -/
theorem findObligation?_sound
    (selection : LoopSelection State Terminal) (region : BlockId)
    (obligation : LoopObligation State)
    (found : selection.findObligation? region = some obligation) :
    obligation ∈ selection.selected ∧ obligation.region = region := by
  constructor
  · exact List.mem_of_find?_eq_some (by
      simpa [findObligation?] using found)
  · have matched : obligation.region == region := List.find?_some
      (p := fun candidate : LoopObligation State => candidate.region == region) (by
        simpa [findObligation?] using found)
    exact LawfulBEq.eq_of_beq matched

/-- Loop-obligation lookup succeeds exactly for an authored selected identity. -/
theorem findObligation?_isSome_iff_mem_selectedIds
    (selection : LoopSelection State Terminal) (region : BlockId) :
    (selection.findObligation? region).isSome = true ↔
      region ∈ selection.selectedIds := by
  simp [findObligation?, selectedIds]

/-- Every selected cyclic-region identity has a concrete obligation. -/
theorem obligationForRegion
    (selection : LoopSelection State Terminal) (region : BlockId)
    (member : region ∈ selection.selectedIds) :
    ∃ obligation, selection.findObligation? region = some obligation := by
  apply Option.isSome_iff_exists.mp
  exact (selection.findObligation?_isSome_iff_mem_selectedIds region).2 member

/-- Executable structural closure check requiring one obligation per discovered
region. It does not discharge the selected invariant or progress description. -/
def wellFormed (selection : LoopSelection State Terminal) : Bool :=
  selection.graph.wellFormed &&
  decide (selection.selectedIds = selection.graph.discoveredLoopIds ∧
    selection.selectedIds.Nodup)

/-- Certificate-facing statement for `LoopSelection.wellFormed`. -/
def WellFormed (selection : LoopSelection State Terminal) : Prop :=
  selection.wellFormed = true

instance (selection : LoopSelection State Terminal) : Decidable selection.WellFormed :=
  inferInstanceAs (Decidable (selection.wellFormed = true))

/-- Public decomposition of exact loop-obligation selection. -/
@[simp] theorem wellFormed_iff (selection : LoopSelection State Terminal) :
    selection.WellFormed ↔
      selection.graph.WellFormed ∧
        selection.selectedIds = selection.graph.discoveredLoopIds ∧
          selection.selectedIds.Nodup := by
  simp [WellFormed, wellFormed, Graph.WellFormed]

/-- A valid loop selection carries a structurally well-formed source graph. -/
theorem graphWellFormed_of_wellFormed
    (selection : LoopSelection State Terminal) (closed : selection.WellFormed) :
    selection.graph.WellFormed :=
  (selection.wellFormed_iff.mp closed).1

/-- A valid loop selection names exactly the structurally discovered regions. -/
theorem selectedIds_eq_discoveredLoopIds_of_wellFormed
    (selection : LoopSelection State Terminal) (closed : selection.WellFormed) :
    selection.selectedIds = selection.graph.discoveredLoopIds :=
  (selection.wellFormed_iff.mp closed).2.1

/-- A valid loop selection contains each cyclic-region identity at most once. -/
theorem selectedIdsNodup_of_wellFormed
    (selection : LoopSelection State Terminal) (closed : selection.WellFormed) :
    selection.selectedIds.Nodup :=
  (selection.wellFormed_iff.mp closed).2.2

private theorem eq_of_mem_of_mem_of_map_nodup
    {α : Type u₁} {β : Type u₂} (key : α → β)
    {items : List α} {left right : α}
    (unique : (items.map key).Nodup)
    (leftMem : left ∈ items) (rightMem : right ∈ items)
    (sameKey : key left = key right) : left = right := by
  induction items with
  | nil => simp at leftMem
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at unique
      rw [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          apply unique.1
          rw [sameKey]
          exact List.mem_map.mpr ⟨right, rightMem, rfl⟩
      · rcases rightMem with rfl | rightMem
        · exfalso
          apply unique.1
          rw [← sameKey]
          exact List.mem_map.mpr ⟨left, leftMem, rfl⟩
        · exact ih unique.2 leftMem rightMem

/-- `LoopSelection.obligation_eq_of_mem_of_mem_of_region_eq` proves that two
members of a valid selection naming the same region are the same obligation. -/
theorem obligation_eq_of_mem_of_mem_of_region_eq
    (selection : LoopSelection State Terminal)
    (left right : LoopObligation State) (closed : selection.WellFormed)
    (leftMem : left ∈ selection.selected) (rightMem : right ∈ selection.selected)
    (sameRegion : left.region = right.region) : left = right := by
  exact eq_of_mem_of_mem_of_map_nodup LoopObligation.region
    (selection.selectedIdsNodup_of_wellFormed closed) leftMem rightMem sameRegion

/-- Under `LoopSelection.WellFormed`, lookup of an authored obligation is
canonical and returns that exact member. -/
theorem findObligation?_eq_some_of_mem
    (selection : LoopSelection State Terminal) (region : BlockId)
    (obligation : LoopObligation State) (closed : selection.WellFormed)
    (member : obligation ∈ selection.selected)
    (hasRegion : obligation.region = region) :
    selection.findObligation? region = some obligation := by
  have regionMember : region ∈ selection.selectedIds := by
    simp [selectedIds]
    exact ⟨obligation, member, hasRegion⟩
  obtain ⟨found, foundLookup⟩ := selection.obligationForRegion region regionMember
  have foundFacts := selection.findObligation?_sound region found foundLookup
  have foundEq : found = obligation :=
    selection.obligation_eq_of_mem_of_mem_of_region_eq found obligation closed
      foundFacts.1 member (foundFacts.2.trans hasRegion.symm)
  simpa [foundEq] using foundLookup

end LoopSelection

end Grass.CFG
