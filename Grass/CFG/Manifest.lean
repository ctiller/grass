import Grass.CFG.Compose

/-!
# Derived CFG manifests

`Manifest.ofComposition` projects block identities, every edge destination,
joins, cyclic regions, call targets/outcome routes, and stack-shape assignments
from one graph-indexed `Composition`.  `ClosedManifest` adds the structural
closure proof without introducing a second authored manifest.
-/

namespace Grass.CFG

universe u v

/-- One graph edge retaining source, exit identity, and exact destination. -/
structure ManifestEdge (Terminal : Type v) where
  source : BlockId
  exit : ExitTag
  target : EdgeTarget Terminal
deriving Repr, DecidableEq

/-- One declared call outcome class. -/
structure CallOutcomeSummary where
  tag : ExitTag
  kind : CallOutcomeKind
deriving Repr, DecidableEq

/-- One routed call return. -/
structure CallReturnSummary (Terminal : Type v) where
  tag : ExitTag
  target : EdgeTarget Terminal
deriving Repr, DecidableEq

/-- Exact inspectable summary of one located call occurrence. -/
structure CallSummary (Terminal : Type v) where
  block : BlockId
  target : CallTarget
  outcomes : List CallOutcomeSummary
  returns : List (CallReturnSummary Terminal)
deriving Repr, DecidableEq

/-- Complete structural projection of one graph composition. -/
structure Manifest (Terminal : Type v) where
  blocks : List BlockId
  edges : List (ManifestEdge Terminal)
  joins : List Graph.JoinDemand
  loops : List Graph.LoopDemand
  calls : List (CallSummary Terminal)
  blockStacks : List BlockStackShape
  edgeStacks : List EdgeStackShape
deriving Repr

namespace Graph

variable {State : Type u} {Terminal : Type v}

/-- Every graph edge in canonical block and outgoing-edge order. -/
def manifestEdges (graph : Graph State Terminal) : List (ManifestEdge Terminal) :=
  graph.blocks.flatMap fun block =>
    block.outgoing.map fun edge => ⟨block.id, edge.exit, edge.target⟩

end Graph

namespace LocatedCall

variable {State : Type u} {Terminal : Type v}

/-- `LocatedCall.summary` projects supported outcomes and routed returns as
separate lists rather than combining them with a truncating zip. -/
def summary (call : LocatedCall State Terminal) : CallSummary Terminal where
  block := call.block
  target := call.site.target
  outcomes := call.site.contract.outcomes.map fun outcome =>
    ⟨outcome.tag, outcome.kind⟩
  returns := call.site.returns.map fun result => ⟨result.tag, result.target⟩

end LocatedCall

namespace Manifest

variable {State : Type u} {Terminal : Type v} {graph : Graph State Terminal}

/-- Derive the complete structural manifest from one graph-indexed composition. -/
def ofComposition (composition : Composition graph) : Manifest Terminal where
  blocks := graph.blockIds
  edges := graph.manifestEdges
  joins := graph.discoverJoins
  loops := graph.discoverLoops
  calls := composition.calls.map LocatedCall.summary
  blockStacks := composition.stacks.blocks
  edgeStacks := composition.stacks.edges

@[simp] theorem ofComposition_blocks (composition : Composition graph) :
    (ofComposition composition).blocks = graph.blockIds := rfl

@[simp] theorem ofComposition_edges (composition : Composition graph) :
    (ofComposition composition).edges = graph.manifestEdges := rfl

@[simp] theorem ofComposition_joins (composition : Composition graph) :
    (ofComposition composition).joins = graph.discoverJoins := rfl

@[simp] theorem ofComposition_loops (composition : Composition graph) :
    (ofComposition composition).loops = graph.discoverLoops := rfl

end Manifest

/-- Structurally closed composition paired with its derived manifest. -/
structure ClosedManifest {State : Type u} {Terminal : Type v}
    (graph : Graph State Terminal) where
  composition : Composition graph
  closed : composition.WellFormed

namespace ClosedManifest

variable {State : Type u} {Terminal : Type v} {graph : Graph State Terminal}

/-- The exact manifest of the closed composition. -/
def manifest (closed : ClosedManifest graph) : Manifest Terminal :=
  Manifest.ofComposition closed.composition

end ClosedManifest

end Grass.CFG
