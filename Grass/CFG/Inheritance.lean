import Grass.CFG.Manifest

/-!
# Single-predecessor entry inheritance

`Graph.incomingEdges` derives every direct incoming edge from the nested graph
source. `Graph.inheritanceCandidate?` returns a source exit contract only when
there is exactly one incoming edge and both its source block and declared exit
resolve. `InheritedEntry` keeps semantic compatibility as an explicit proof;
structural discovery alone does not establish it.
-/

namespace Grass.CFG

universe u v

/-- One direct incoming edge, retaining its source and exit identity. -/
structure IncomingEdge where
  source : BlockId
  exit : ExitTag
deriving Repr, DecidableEq

/-- Comparable identity of one single-predecessor inheritance candidate. -/
structure InheritanceKey where
  target : BlockId
  source : BlockId
  exit : ExitTag
deriving Repr, DecidableEq

/-- Structurally discovered source exit for a target with one incoming edge. -/
structure InheritanceCandidate (State : Type u) where
  target : BlockId
  incoming : IncomingEdge
  exitContract : ExitContract State

namespace InheritanceCandidate

variable {State : Type u}

/-- Comparable structural identity of an inheritance candidate. -/
def key (candidate : InheritanceCandidate State) : InheritanceKey :=
  ⟨candidate.target, candidate.incoming.source, candidate.incoming.exit⟩

end InheritanceCandidate

namespace Graph

variable {State : Type u} {Terminal : Type v}

/-- Every direct edge entering `target`, preserving block and outgoing-edge
order and retaining repeated malformed raw edges. -/
def incomingEdges (graph : Graph State Terminal) (target : BlockId) :
    List IncomingEdge :=
  graph.blocks.flatMap fun block =>
    block.outgoing.filterMap fun edge =>
      match edge.target with
      | .block id => if id = target then some ⟨block.id, edge.exit⟩ else none
      | .terminal _ => none

/-- Find one declared source exit contract by tag. -/
def findExitContract? (block : Block State Terminal) (tag : ExitTag) :
    Option (ExitContract State) :=
  block.contract.exits.find? fun exit => exit.tag == tag

/-- Discover the exact source exit that may supply a target entry contract.
Targets with zero or multiple incoming edges have no inheritance candidate. -/
def inheritanceCandidate? (graph : Graph State Terminal) (target : BlockId) :
    Option (InheritanceCandidate State) :=
  match graph.incomingEdges target with
  | [incoming] =>
      match graph.findBlock? incoming.source with
      | none => none
      | some source =>
          match findExitContract? source incoming.exit with
          | none => none
          | some exitContract => some ⟨target, incoming, exitContract⟩
  | _ => none

/-- Comparable projection of `Graph.inheritanceCandidate?`. -/
def inheritanceKey? (graph : Graph State Terminal) (target : BlockId) :
    Option InheritanceKey :=
  (graph.inheritanceCandidate? target).map InheritanceCandidate.key

end Graph

/-- Proof that one exact structural candidate establishes the target block's
authored entry predicate. -/
structure InheritedEntry {State : Type u} {Terminal : Type v}
    (graph : Graph State Terminal) (target : BlockId) where
  candidate : InheritanceCandidate State
  candidateExact : graph.inheritanceCandidate? target = some candidate
  targetBlock : Block State Terminal
  targetExact : graph.findBlock? target = some targetBlock
  compatible : ∀ state, candidate.exitContract.ensures state ↔
    targetBlock.contract.requires state

end Grass.CFG
