import Grass.CFG.Contract

/-!
# ISA-neutral control-flow graphs

Edges are nested under their source block.  Labels, predecessor sets, direct
targets, and closure checks are consequently projections of one graph value;
an author cannot keep a parallel edge or predecessor manifest that drifts from
the source.
-/

namespace Grass.CFG

universe u v

/-- A CFG edge either enters another block or reaches a caller-supplied
terminal disposition. -/
inductive EdgeTarget (Terminal : Type v) where
  | block (id : BlockId)
  | terminal (disposition : Terminal)
deriving Repr, DecidableEq, BEq

/-- One named exit and its control-flow destination. -/
structure Edge (Terminal : Type v) where
  exit : ExitTag
  target : EdgeTarget Terminal
deriving Repr, DecidableEq, BEq

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

/-- Find one block by stable identity.  Structural well-formedness guarantees
that a successful result is unique. -/
def findBlock? (graph : Graph State Terminal) (id : BlockId) :
    Option (Block State Terminal) :=
  graph.blocks.find? (fun block => block.id == id)

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

/-- Exact predecessor discovery from the nested edge lists.

One predecessor identity occurs per source block, even when malformed raw input
contains two edges from that block to the same target.  A well-formed graph also
has unique block identities, so its result has no duplicates.
-/
def predecessors (graph : Graph State Terminal) (target : BlockId) : List BlockId :=
  (graph.blocks.filter fun block => hasDirectEdgeTo block target).map Block.id

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
  (outgoingTags block).eraseDups.length == (outgoingTags block).length

/-- Every direct edge resolves to a block in the same graph.  Terminal
dispositions are values supplied by the surrounding contract and need no label
resolution here. -/
def targetsResolved (graph : Graph State Terminal) : Bool :=
  graph.blocks.all fun block =>
    block.outgoing.all fun edge =>
      match edge.target with
      | .block id => (graph.findBlock? id).isSome
      | .terminal _ => true

/-- Executable structural closure check.

This checks exactly the information available before symbolic execution:
unique block identities, a resolved entry, unique declared-and-covered exits,
and resolved direct targets.  It does not claim local instruction correctness.
-/
def wellFormed (graph : Graph State Terminal) : Bool :=
  graph.blockIds.eraseDups.length == graph.blockIds.length &&
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

/-- Public decomposition of structural graph closure.  Certificate consumers
use these four facts rather than unfolding the checker implementation. -/
@[simp] theorem wellFormed_iff (graph : Graph State Terminal) :
    graph.WellFormed ↔
      ((graph.blockIds.eraseDups.length = graph.blockIds.length ∧
        (graph.findBlock? graph.entry).isSome = true) ∧
        (graph.blocks.all fun block =>
          block.contract.wellFormed &&
          outgoingUnique block &&
          edgesDeclared block &&
          exitsCovered block) = true) ∧
        graph.targetsResolved = true := by
  simp [WellFormed, wellFormed]

end Graph

end Grass.CFG
