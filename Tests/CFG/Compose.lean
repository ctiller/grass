import Grass.CFG.Compose

/-!
# CFG structural composition fixtures

The fixtures close a diamond graph and reject missing stack assignments,
scope-bypassing edges, unresolved local calls, and unresolved return targets.
-/

namespace Grass.Tests.CFG.Compose

open Grass Grass.CFG

def blockId (name : String) : BlockId := ⟨⟨"test.compose", name⟩⟩
def exitTag (name : String) : ExitTag := ⟨⟨"test.compose", name⟩⟩
def scopeId (name : String) : StackScopeId := ⟨⟨"test.compose", name⟩⟩

inductive Terminal where
  | returned
  | failed
deriving Repr, DecidableEq

def contract (tags : List String) : BlockContract Nat where
  requires := fun _ => True
  exits := tags.map fun name => ⟨exitTag name, fun _ => True⟩

def edge (tag target : String) : Edge Terminal :=
  ⟨exitTag tag, .block (blockId target)⟩

def terminalEdge (tag : String) : Edge Terminal :=
  ⟨exitTag tag, .terminal .returned⟩

def block (name : String) (tags : List String) (outgoing : List (Edge Terminal)) :
    Block Nat Terminal :=
  ⟨blockId name, contract tags, outgoing⟩

def graph : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [
    block "entry" ["left", "right"] [edge "left" "left", edge "right" "right"],
    block "left" ["next"] [edge "next" "join"],
    block "right" ["next"] [edge "next" "join"],
    block "join" ["return"] [terminalEdge "return"]
  ]

def plain : StackShape := ⟨32, []⟩

def stacks : StackAssignment graph where
  blocks := graph.blockIds.map fun id => ⟨id, plain⟩
  edges := graph.edgeKeys.map fun key => ⟨key, plain⟩

example : stacks.WellFormed := by decide

def joins : JoinSelection graph where
  selected := [blockId "join"]

def loops : LoopSelection graph where
  selected := []

def composition : Composition graph where
  joins := joins
  loops := loops
  stacks := stacks
  calls := []

example : composition.WellFormed := by decide

def missingBlockShape : StackAssignment graph := {
  stacks with blocks := stacks.blocks.drop 1
}
example : ¬ missingBlockShape.WellFormed := by decide

def reorderedBlocks : StackAssignment graph := {
  stacks with blocks := stacks.blocks.reverse
}
example : ¬ reorderedBlocks.WellFormed := by decide

def duplicateEdgeShape : StackAssignment graph := {
  stacks with edges :=
    ⟨⟨blockId "entry", exitTag "left"⟩, plain⟩ :: stacks.edges
}
example : ¬ duplicateEdgeShape.WellFormed := by decide

def liveScope : StackShape := ⟨32, [scopeId "live"]⟩

def bypassedScope : StackAssignment graph := {
  stacks with edges := stacks.edges.map fun entry =>
    if entry.edge = ⟨blockId "left", exitTag "next"⟩ then
      { entry with shape := liveScope }
    else
      entry
}
example : ¬ bypassedScope.WellFormed := by decide

def localContract : CallContract Nat where
  requires := fun _ => True
  entryStack := plain
  outcomes := [⟨exitTag "normal", .normal, fun _ => True, plain⟩]

def localCall (target : String) (returnTarget : String) : LocatedCall Nat Terminal where
  block := blockId "entry"
  site := {
    target := .local (blockId target)
    contract := localContract
    actualEntryStack := plain
    returns := [⟨exitTag "normal", .block (blockId returnTarget)⟩]
  }

example : (localCall "left" "join").closedIn graph := by decide
example : ¬ (localCall "missing" "join").closedIn graph := by decide
example : ¬ (localCall "left" "missing").closedIn graph := by decide

def misplacedCall : LocatedCall Nat Terminal := {
  localCall "left" "join" with block := blockId "missing"
}
example : ¬ misplacedCall.closedIn graph := by decide

def withCall : Composition graph := {
  composition with calls := [localCall "left" "join"]
}
example : withCall.WellFormed := by decide

def unresolvedCall : Composition graph := {
  composition with calls := [localCall "missing" "join"]
}
example : ¬ unresolvedCall.WellFormed := by decide

end Grass.Tests.CFG.Compose
