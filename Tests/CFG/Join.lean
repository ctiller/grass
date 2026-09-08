import Grass.CFG.Join

/-!
# Structural join discovery fixtures

The fixtures pin canonical predecessor order, cycle reporting, and rejection of
missing, extra, duplicate, or reordered join selections.
-/

namespace Grass.Tests.CFG.Join

open Grass Grass.CFG

def blockId (name : String) : BlockId := ⟨⟨"test.join", name⟩⟩
def exitTag (name : String) : ExitTag := ⟨⟨"test.join", name⟩⟩

inductive Terminal where
  | returned
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

def diamond : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [
    block "entry" ["left", "right"] [edge "left" "left", edge "right" "right"],
    block "left" ["next"] [edge "next" "join"],
    block "right" ["next"] [edge "next" "join"],
    block "join" ["return"] [terminalEdge "return"]
  ]

example : diamond.WellFormed := by decide

example : diamond.discoverJoins = [{
    id := blockId "join"
    predecessors := [blockId "left", blockId "right"]
    cyclic := false
  }] := by decide

example : diamond.reachable (blockId "entry") (blockId "join") := by decide
example : ¬ diamond.reachable (blockId "join") (blockId "entry") := by decide

def repeatedEdgeSource : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [
    block "entry" ["first", "second"]
      [edge "first" "target", edge "second" "target"],
    block "target" ["return"] [terminalEdge "return"]
  ]

example : repeatedEdgeSource.WellFormed := by decide
example : repeatedEdgeSource.predecessors (blockId "target") =
    [blockId "entry"] := by decide
example : repeatedEdgeSource.discoverJoins = [] := by decide

def looped : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [
    block "entry" ["next"] [edge "next" "header"],
    block "header" ["body", "done"] [edge "body" "body", edge "done" "done"],
    block "body" ["back"] [edge "back" "header"],
    block "done" ["return"] [terminalEdge "return"]
  ]

example : looped.WellFormed := by decide
example : looped.cyclicAt (blockId "header") := by decide
example : looped.cyclicAt (blockId "body") := by decide

example : looped.discoverJoins = [{
    id := blockId "header"
    predecessors := [blockId "entry", blockId "body"]
    cyclic := true
  }] := by decide

def selected : JoinSelection Nat Terminal where
  graph := diamond
  selected := [blockId "join"]

example : selected.WellFormed := by decide

example : ({ graph := repeatedEdgeSource, selected := [] } :
    JoinSelection Nat Terminal).WellFormed := by decide

def missing : JoinSelection Nat Terminal := { selected with selected := [] }
example : ¬ missing.WellFormed := by decide

def extra : JoinSelection Nat Terminal := {
  selected with selected := [
    blockId "join",
    blockId "left"
  ]
}
example : ¬ extra.WellFormed := by decide

def duplicate : JoinSelection Nat Terminal := {
  selected with selected := [
    blockId "join",
    blockId "join"
  ]
}
example : ¬ duplicate.WellFormed := by decide

def twoJoins : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [
    block "entry" ["left", "right"] [edge "left" "left", edge "right" "right"],
    block "left" ["first"] [edge "first" "first"],
    block "right" ["first"] [edge "first" "first"],
    block "first" ["left", "right"] [edge "left" "left2", edge "right" "right2"],
    block "left2" ["second"] [edge "second" "second"],
    block "right2" ["second"] [edge "second" "second"],
    block "second" ["return"] [terminalEdge "return"]
  ]

def reversed : JoinSelection Nat Terminal where
  graph := twoJoins
  selected := [
    blockId "second",
    blockId "first"
  ]

example : twoJoins.discoveredJoinIds = [blockId "first", blockId "second"] := by decide
example : ¬ reversed.WellFormed := by decide

end Grass.Tests.CFG.Join
