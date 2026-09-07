import Grass.CFG.Loop

/-!
# Structural loop-region fixtures

The fixtures cover a two-block loop, a singleton self-loop, canonical region
ordering, measure and frontier declarations, and exact-selection rejection.
-/

namespace Grass.Tests.CFG.Loop

open Grass Grass.CFG

def blockId (name : String) : BlockId := ⟨⟨"test.loop", name⟩⟩
def exitTag (name : String) : ExitTag := ⟨⟨"test.loop", name⟩⟩

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

def graph : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [
    block "entry" ["first"] [edge "first" "header"],
    block "header" ["body", "done"] [edge "body" "body", edge "done" "done"],
    block "body" ["back"] [edge "back" "header"],
    block "done" ["spin"] [edge "spin" "done"]
  ]

example : graph.WellFormed := by decide

example : graph.loopRegionMembers (blockId "body") =
    [blockId "header", blockId "body"] := by decide

example : graph.discoverLoops = [
    ⟨blockId "header", [blockId "header", blockId "body"]⟩,
    ⟨blockId "done", [blockId "done"]⟩
  ] := by decide

def headerObligation : LoopObligation Nat where
  region := blockId "header"
  invariant := fun state => state ≤ 10
  progress := .measure fun state => 10 - state

def doneObligation : LoopObligation Nat where
  region := blockId "done"
  invariant := fun _ => True
  progress := .frontier fun before after => before < after

def selected : LoopSelection graph where
  selected := [headerObligation, doneObligation]

example : selected.WellFormed := by decide

def missing : LoopSelection graph := {
  selected with selected := [headerObligation]
}
example : ¬ missing.WellFormed := by decide

def duplicate : LoopSelection graph := {
  selected with selected := [headerObligation, headerObligation, doneObligation]
}
example : ¬ duplicate.WellFormed := by decide

def reordered : LoopSelection graph := {
  selected with selected := [doneObligation, headerObligation]
}
example : ¬ reordered.WellFormed := by decide

def acyclic : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [
    block "entry" ["done"] [edge "done" "exit"],
    block "exit" ["return"] [terminalEdge "return"]
  ]

example : acyclic.WellFormed := by decide
example : acyclic.discoverLoops = [] := by decide

end Grass.Tests.CFG.Loop
