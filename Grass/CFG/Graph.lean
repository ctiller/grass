import Grass.CFG.Contract

/-!
# ISA-neutral control-flow graphs

Edges are nested under their source block.  Labels, predecessor sets, direct
targets, and closure checks are consequently projections of one graph value;
`Graph.predecessors` and `Graph.directTargets` derive both views without a
separately authored edge or predecessor manifest.
-/

namespace Grass.CFG

universe u v

/-- A CFG edge either enters another block or reaches a caller-supplied
terminal disposition. -/
inductive EdgeTarget (Terminal : Type v) where
  | block (id : BlockId)
  | terminal (disposition : Terminal)
deriving Repr, DecidableEq

/-- One named exit and its control-flow destination. -/
structure Edge (Terminal : Type v) where
  exit : ExitTag
  target : EdgeTarget Terminal
deriving Repr, DecidableEq

/-- Canonical identity of an edge inside its source graph. -/
structure EdgeKey where
  source : BlockId
  exit : ExitTag
deriving Repr, DecidableEq

/-- An authored edge paired with the identity of its structural source block. -/
structure LocatedEdge (Terminal : Type v) where
  source : BlockId
  edge : Edge Terminal
deriving Repr, DecidableEq

def LocatedEdge.key {Terminal : Type v} (located : LocatedEdge Terminal) : EdgeKey :=
  ⟨located.source, located.edge.exit⟩

/-- A basic block with its contract and structurally authored outgoing edges. -/
structure Block (State : Type u) (Terminal : Type v) where
  id : BlockId
  contract : BlockContract State
  outgoing : List (Edge Terminal)

/-- A finite control-flow graph with one selected entry block. -/
structure Graph (State : Type u) (Terminal : Type v) where
  entry : BlockId
  blocks : List (Block State Terminal)

namespace Graph

variable {State : Type u} {Terminal : Type v}

/-- Block identities in structural source order. -/
def blockIds (graph : Graph State Terminal) : List BlockId :=
  graph.blocks.map Block.id

/-- Edges flattened in canonical block and outgoing-edge order, retaining each
structural source identity. -/
def locatedEdges (graph : Graph State Terminal) : List (LocatedEdge Terminal) :=
  graph.blocks.flatMap fun block =>
    block.outgoing.map fun edge => ⟨block.id, edge⟩

/-- Canonical edge identities in structural source order. -/
def edgeKeys (graph : Graph State Terminal) : List EdgeKey :=
  graph.locatedEdges.map LocatedEdge.key

@[simp] theorem mem_locatedEdges_iff
    (graph : Graph State Terminal) (source : BlockId) (edge : Edge Terminal) :
    (⟨source, edge⟩ : LocatedEdge Terminal) ∈ graph.locatedEdges ↔
      ∃ block ∈ graph.blocks, block.id = source ∧ edge ∈ block.outgoing := by
  constructor
  · rw [locatedEdges, List.mem_flatMap]
    rintro ⟨block, blockMember, mappedMember⟩
    rcases List.mem_map.mp mappedMember with ⟨candidate, edgeMember, exactLocated⟩
    cases exactLocated
    exact ⟨block, blockMember, rfl, edgeMember⟩
  · rintro ⟨block, blockMember, sourceExact, edgeMember⟩
    rw [locatedEdges, List.mem_flatMap]
    refine ⟨block, blockMember, ?_⟩
    apply List.mem_map.mpr
    exact ⟨edge, edgeMember, by simp [sourceExact]⟩

/-- Find the first authored occurrence of one canonical edge identity.  The
flattened search is total even for malformed graphs with duplicate block ids. -/
def findEdge? (graph : Graph State Terminal) (key : EdgeKey) :
    Option (LocatedEdge Terminal) :=
  graph.locatedEdges.find? fun located => located.key == key

/-- A successful edge lookup returns an authored occurrence with the requested
canonical identity. -/
theorem findEdge?_sound
    (graph : Graph State Terminal) (key : EdgeKey)
    (located : LocatedEdge Terminal)
    (hfind : graph.findEdge? key = some located) :
    located ∈ graph.locatedEdges ∧ located.key = key := by
  constructor
  · exact List.mem_of_find?_eq_some (by
      simpa [findEdge?] using hfind)
  · have matched : located.key == key := List.find?_some
      (p := fun candidate : LocatedEdge Terminal => candidate.key == key) (by
        simpa [findEdge?] using hfind)
    exact LawfulBEq.eq_of_beq matched

/-- Edge lookup succeeds exactly for canonical identities present in structural
source order. -/
theorem findEdge?_isSome_iff_mem_edgeKeys
    (graph : Graph State Terminal) (key : EdgeKey) :
    (graph.findEdge? key).isSome = true ↔ key ∈ graph.edgeKeys := by
  simp [findEdge?, edgeKeys]

/-- Every structural edge identity has a concrete located lookup result. -/
theorem edgeForKey
    (graph : Graph State Terminal) (key : EdgeKey)
    (member : key ∈ graph.edgeKeys) :
    ∃ located, graph.findEdge? key = some located := by
  apply Option.isSome_iff_exists.mp
  exact (graph.findEdge?_isSome_iff_mem_edgeKeys key).2 member

/-- Find one block by stable identity.  For a `Graph.WellFormed` value the block
identities are unique, so a successful result denotes one structural block. -/
def findBlock? (graph : Graph State Terminal) (id : BlockId) :
    Option (Block State Terminal) :=
  graph.blocks.find? (fun block => block.id == id)

/-- A successful block lookup returns a structural member with the requested
identity. -/
theorem findBlock?_sound
    (graph : Graph State Terminal) (id : BlockId)
    (block : Block State Terminal)
    (hfind : graph.findBlock? id = some block) :
    block ∈ graph.blocks ∧ block.id = id := by
  constructor
  · exact List.mem_of_find?_eq_some (by
      simpa [findBlock?] using hfind)
  · have matched : block.id == id := List.find?_some
      (p := fun candidate : Block State Terminal => candidate.id == id) (by
        simpa [findBlock?] using hfind)
    exact LawfulBEq.eq_of_beq matched

/-- Block lookup succeeds exactly for identities present in structural source. -/
theorem findBlock?_isSome_iff_mem_blockIds
    (graph : Graph State Terminal) (id : BlockId) :
    (graph.findBlock? id).isSome = true ↔ id ∈ graph.blockIds := by
  simp [findBlock?, blockIds]

/-- Every structural block identity has a concrete lookup result. -/
theorem blockForId
    (graph : Graph State Terminal) (id : BlockId)
    (member : id ∈ graph.blockIds) :
    ∃ block, graph.findBlock? id = some block := by
  apply Option.isSome_iff_exists.mp
  exact (graph.findBlock?_isSome_iff_mem_blockIds id).2 member

/-- Direct block targets, retaining source and edge order. -/
def directTargets (graph : Graph State Terminal) : List BlockId :=
  graph.blocks.flatMap fun block =>
    block.outgoing.filterMap fun edge =>
      match edge.target with
      | .block id => some id
      | .terminal _ => none

/-- Direct target identities for which no block exists. -/
def unresolvedTargets (graph : Graph State Terminal) : List BlockId :=
  graph.directTargets.filter fun id => (graph.findBlock? id).isNone

/-- Whether a block contains at least one direct edge to `target`. -/
def hasDirectEdgeTo (block : Block State Terminal) (target : BlockId) : Bool :=
  block.outgoing.any fun edge =>
    match edge.target with
    | .block id => id == target
    | .terminal _ => false

/-- A positive direct-edge query exposes one exact structural edge witness. -/
theorem hasDirectEdgeTo_eq_true_iff
    (block : Block State Terminal) (target : BlockId) :
    hasDirectEdgeTo block target = true ↔
      ∃ edge ∈ block.outgoing, edge.target = .block target := by
  constructor
  · rw [hasDirectEdgeTo, List.any_eq_true]
    rintro ⟨edge, member, matched⟩
    refine ⟨edge, member, ?_⟩
    cases targetShape : edge.target with
    | block id =>
        simp [targetShape] at matched
        simp [matched]
    | terminal disposition =>
        simp [targetShape] at matched
  · rintro ⟨edge, member, targetExact⟩
    rw [hasDirectEdgeTo, List.any_eq_true]
    refine ⟨edge, member, ?_⟩
    simp [targetExact]

/-- Exact predecessor discovery from the nested edge lists.

One predecessor identity occurs per source block, even when malformed raw input
contains two edges from that block to the same target.  A well-formed graph also
has unique block identities, so its result has no duplicates.
-/
def predecessors (graph : Graph State Terminal) (target : BlockId) : List BlockId :=
  (graph.blocks.filter fun block => hasDirectEdgeTo block target).map Block.id

/-- Predecessor membership is exactly membership of a source block carrying one
direct edge to the requested target. -/
theorem mem_predecessors_iff
    (graph : Graph State Terminal) (source target : BlockId) :
    source ∈ graph.predecessors target ↔
      ∃ block ∈ graph.blocks,
        block.id = source ∧
          ∃ edge ∈ block.outgoing, edge.target = .block target := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨block, selected, identity⟩
    rcases List.mem_filter.mp selected with ⟨structural, hasEdge⟩
    exact ⟨block, structural, identity,
      (hasDirectEdgeTo_eq_true_iff block target).mp hasEdge⟩
  · rintro ⟨block, structural, identity, hasEdge⟩
    apply List.mem_map.mpr
    exact ⟨block, List.mem_filter.mpr ⟨structural,
      (hasDirectEdgeTo_eq_true_iff block target).mpr hasEdge⟩, identity⟩

/-- The outgoing exit identities of one block. -/
def outgoingTags (block : Block State Terminal) : List ExitTag :=
  block.outgoing.map Edge.exit

/-- Every edge names an exit declared by its source contract. -/
def edgesDeclared (block : Block State Terminal) : Bool :=
  block.outgoing.all fun edge => block.contract.declaresExit edge.exit

/-- Every declared contract exit has a corresponding CFG edge. -/
def exitsCovered (block : Block State Terminal) : Bool :=
  block.contract.exits.all fun exit => (outgoingTags block).contains exit.tag

/-- Each declared exit selects at most one destination. -/
def outgoingUnique (block : Block State Terminal) : Bool :=
  decide (outgoingTags block).Nodup

/-- Every direct edge resolves to a block in the same graph.  Terminal
dispositions are values supplied by the surrounding contract and need no label
resolution here. -/
def targetsResolved (graph : Graph State Terminal) : Bool :=
  graph.blocks.all fun block =>
    block.outgoing.all fun edge =>
      match edge.target with
      | .block id => (graph.findBlock? id).isSome
      | .terminal _ => true

/-- Proposition-level structural conditions checked locally for one block. -/
def BlockStructurallyClosed (block : Block State Terminal) : Prop :=
  ((block.contract.WellFormed ∧
    (outgoingTags block).Nodup) ∧
    (∀ edge ∈ block.outgoing, edge.exit ∈ block.contract.exitTags)) ∧
    (∀ exit ∈ block.contract.exits, exit.tag ∈ outgoingTags block)

/-- Proposition-level direct-target closure for every structural edge. -/
def TargetsResolved (graph : Graph State Terminal) : Prop :=
  ∀ block ∈ graph.blocks, ∀ edge ∈ block.outgoing,
    (match edge.target with
    | .block id => (graph.findBlock? id).isSome
    | .terminal _ => true) = true

/-- Executable structural closure check.

This checks exactly the information available before symbolic execution:
unique block identities, a resolved entry, unique declared-and-covered exits,
and resolved direct targets.  It does not claim local instruction correctness.
-/
def wellFormed (graph : Graph State Terminal) : Bool :=
  decide graph.blockIds.Nodup &&
  (graph.findBlock? graph.entry).isSome &&
  (graph.blocks.all fun block =>
    block.contract.wellFormed &&
    outgoingUnique block &&
    edgesDeclared block &&
    exitsCovered block) &&
  graph.targetsResolved

/-- Certificate-facing statement of structural graph closure. -/
def WellFormed (graph : Graph State Terminal) : Prop := graph.wellFormed = true

instance (graph : Graph State Terminal) : Decidable graph.WellFormed :=
  inferInstanceAs (Decidable (graph.wellFormed = true))

/-- Public proposition-level decomposition of structural graph closure. -/
@[simp] theorem wellFormed_iff (graph : Graph State Terminal) :
    graph.WellFormed ↔
      ((graph.blockIds.Nodup ∧
        (graph.findBlock? graph.entry).isSome = true) ∧
        (∀ block ∈ graph.blocks, BlockStructurallyClosed block)) ∧
        graph.TargetsResolved := by
  simp [WellFormed, wellFormed, BlockStructurallyClosed, TargetsResolved,
    BlockContract.WellFormed, BlockContract.wellFormed, outgoingUnique,
    edgesDeclared, exitsCovered, targetsResolved, BlockContract.declaresExit,
    BlockContract.exitTags]

/-- `Graph.blockIdsNodup_of_wellFormed` projects unique structural identities. -/
theorem blockIdsNodup_of_wellFormed
    (graph : Graph State Terminal) (closed : graph.WellFormed) :
    graph.blockIds.Nodup :=
  (graph.wellFormed_iff.mp closed).1.1.1

/-- `Graph.entryResolved_of_wellFormed` projects entry lookup success. -/
theorem entryResolved_of_wellFormed
    (graph : Graph State Terminal) (closed : graph.WellFormed) :
    (graph.findBlock? graph.entry).isSome = true :=
  (graph.wellFormed_iff.mp closed).1.1.2

/-- `Graph.blockClosed_of_wellFormed` projects the proposition-level local
conditions for any structural block. -/
theorem blockClosed_of_wellFormed
    (graph : Graph State Terminal) (closed : graph.WellFormed)
    (block : Block State Terminal) (member : block ∈ graph.blocks) :
    BlockStructurallyClosed block :=
  (graph.wellFormed_iff.mp closed).1.2 block member

/-- `Graph.targetsResolved_of_wellFormed` projects proposition-level target
closure for every structural edge. -/
theorem targetsResolved_of_wellFormed
    (graph : Graph State Terminal) (closed : graph.WellFormed) :
    graph.TargetsResolved :=
  (graph.wellFormed_iff.mp closed).2

end Graph

end Grass.CFG
