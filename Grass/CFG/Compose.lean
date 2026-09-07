import Grass.CFG.Call
import Grass.CFG.Loop

/-!
# CFG boundary composition

`Composition.wellFormed` closes the structural seams between graph edges, stack
shapes, join/loop selections, and explicitly supplied call sites.  Semantic
block certificates are intended as a later input; this module defines no
semantic block-certificate constructor.
-/

namespace Grass.CFG

universe u v

/-- Canonical identity of one graph edge. -/
structure EdgeKey where
  source : BlockId
  exit : ExitTag
deriving Repr, DecidableEq

namespace Graph

variable {State : Type u} {Terminal : Type v}

/-- Edge identities in canonical block and outgoing-edge order. -/
def edgeKeys (graph : Graph State Terminal) : List EdgeKey :=
  graph.blocks.flatMap fun block =>
    block.outgoing.map fun edge => ⟨block.id, edge.exit⟩

end Graph

/-- Entry stack shape assigned to one block. -/
structure BlockStackShape where
  block : BlockId
  shape : StackShape
deriving Repr, DecidableEq

/-- Stack shape established by one block exit. -/
structure EdgeStackShape where
  edge : EdgeKey
  shape : StackShape
deriving Repr, DecidableEq

/-- Exact stack-boundary assignment for one graph. -/
structure StackAssignment {State : Type u} {Terminal : Type v}
    (graph : Graph State Terminal) where
  blocks : List BlockStackShape
  edges : List EdgeStackShape

namespace StackAssignment

variable {State : Type u} {Terminal : Type v} {graph : Graph State Terminal}

/-- Assigned block identities in authored order. -/
def blockIds (assignment : StackAssignment graph) : List BlockId :=
  assignment.blocks.map BlockStackShape.block

/-- Assigned edge identities in authored order. -/
def edgeKeys (assignment : StackAssignment graph) : List EdgeKey :=
  assignment.edges.map EdgeStackShape.edge

/-- Find a block-entry stack shape by identity. -/
def findBlockShape? (assignment : StackAssignment graph) (id : BlockId) :
    Option StackShape :=
  (assignment.blocks.find? fun entry => entry.block == id).map BlockStackShape.shape

/-- Find an edge-exit stack shape by canonical edge identity. -/
def findEdgeShape? (assignment : StackAssignment graph) (key : EdgeKey) :
    Option StackShape :=
  (assignment.edges.find? fun entry => entry.edge == key).map EdgeStackShape.shape

/-- Whether every direct edge establishes exactly the target block's entry
shape.  Terminal edges have no in-graph target but still receive an exit shape
through the exact edge-key assignment. -/
def directEdgesCompatible (assignment : StackAssignment graph) : Bool :=
  graph.blocks.all fun block =>
    block.outgoing.all fun edge =>
      match edge.target with
      | .terminal _ => true
      | .block target =>
          match assignment.findEdgeShape? ⟨block.id, edge.exit⟩,
              assignment.findBlockShape? target with
          | some actual, some expected => actual.compatible expected
          | _, _ => false

/-- Executable stack-boundary closure check. -/
def wellFormed (assignment : StackAssignment graph) : Bool :=
  graph.wellFormed &&
  decide (assignment.blockIds = graph.blockIds) &&
  decide (assignment.edgeKeys = graph.edgeKeys) &&
  (assignment.blocks.all fun entry => entry.shape.wellFormed) &&
  (assignment.edges.all fun entry => entry.shape.wellFormed) &&
  assignment.directEdgesCompatible

/-- Certificate-facing statement for `StackAssignment.wellFormed`. -/
def WellFormed (assignment : StackAssignment graph) : Prop :=
  assignment.wellFormed = true

instance (assignment : StackAssignment graph) : Decidable assignment.WellFormed :=
  inferInstanceAs (Decidable (assignment.wellFormed = true))

end StackAssignment

namespace CallSite

variable {State : Type u} {Terminal : Type v}

/-- Whether a local call target resolves in the enclosing graph. -/
def targetResolved (site : CallSite State Terminal) (graph : Graph State Terminal) : Bool :=
  match site.target with
  | .local entry => (graph.findBlock? entry).isSome
  | .external _ => true

/-- Whether every in-graph return target resolves. -/
def returnsResolved (site : CallSite State Terminal) (graph : Graph State Terminal) : Bool :=
  site.returns.all fun result =>
    match result.target with
    | .block id => (graph.findBlock? id).isSome
    | .terminal _ => true

/-- Local call-site closure inside an enclosing graph. -/
def closedIn (site : CallSite State Terminal) (graph : Graph State Terminal) : Bool :=
  site.wellFormed && site.targetResolved graph && site.returnsResolved graph

end CallSite

/-- A call occurrence located in its containing graph block. -/
structure LocatedCall (State : Type u) (Terminal : Type v) where
  block : BlockId
  site : CallSite State Terminal

namespace LocatedCall

variable {State : Type u} {Terminal : Type v}

/-- Structural closure of a located call occurrence. -/
def closedIn (call : LocatedCall State Terminal) (graph : Graph State Terminal) : Bool :=
  (graph.findBlock? call.block).isSome && call.site.closedIn graph

end LocatedCall

/-- All structural inputs needed before semantic block certificates can be
plugged together.  Every component is indexed by the same graph. -/
structure Composition {State : Type u} {Terminal : Type v}
    (graph : Graph State Terminal) where
  joins : JoinSelection graph
  loops : LoopSelection graph
  stacks : StackAssignment graph
  calls : List (LocatedCall State Terminal)

namespace Composition

variable {State : Type u} {Terminal : Type v} {graph : Graph State Terminal}

/-- Executable structural composition check. -/
def wellFormed (composition : Composition graph) : Bool :=
  composition.joins.wellFormed &&
  composition.loops.wellFormed &&
  composition.stacks.wellFormed &&
  composition.calls.all fun call => call.closedIn graph

/-- Certificate-facing statement for `Composition.wellFormed`. -/
def WellFormed (composition : Composition graph) : Prop :=
  composition.wellFormed = true

instance (composition : Composition graph) : Decidable composition.WellFormed :=
  inferInstanceAs (Decidable (composition.wellFormed = true))

end Composition

end Grass.CFG
