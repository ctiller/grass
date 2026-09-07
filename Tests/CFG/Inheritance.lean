import Grass.CFG.Inheritance
import Tests.CFG.Compose

/-!
# CFG entry-inheritance fixtures

The diamond graph exposes candidates at its single-predecessor arms, none at
its entry or shared join, and preserves repeated incoming edge occurrences.
-/

namespace Grass.Tests.CFG.Inheritance

open Grass Grass.CFG
open Grass.Tests.CFG.Compose

example : graph.incomingEdges (blockId "left") =
    [⟨blockId "entry", exitTag "left"⟩] := by native_decide

example : graph.inheritanceKey? (blockId "left") =
    some ⟨blockId "left", blockId "entry", exitTag "left"⟩ := by native_decide

example : graph.inheritanceKey? (blockId "entry") = none := by native_decide
example : graph.inheritanceKey? (blockId "join") = none := by native_decide

def repeatedIncoming : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [
    block "entry" ["left", "right"] [edge "left" "left", edge "right" "left"],
    block "left" ["return"] [terminalEdge "return"]
  ]

example : repeatedIncoming.incomingEdges (blockId "left") = [
    ⟨blockId "entry", exitTag "left"⟩,
    ⟨blockId "entry", exitTag "right"⟩
  ] := by native_decide

example : repeatedIncoming.inheritanceKey? (blockId "left") = none := by
  native_decide

def straightContract (required : Nat) : BlockContract Nat where
  requires := fun state => state = required
  exits := [⟨exitTag "next", fun state => state = required⟩]

def straightSource : Block Nat Terminal :=
  ⟨blockId "source", straightContract 7,
    [⟨exitTag "next", .block (blockId "target")⟩]⟩

def straightTarget : Block Nat Terminal :=
  ⟨blockId "target", straightContract 7,
    [⟨exitTag "next", .terminal .returned⟩]⟩

def straightGraph : Graph Nat Terminal where
  entry := blockId "source"
  blocks := [straightSource, straightTarget]

def inherited : InheritedEntry straightGraph (blockId "target") where
  candidate := ⟨blockId "target", ⟨blockId "source", exitTag "next"⟩,
    ⟨exitTag "next", fun state => state = 7⟩⟩
  candidateExact := rfl
  targetBlock := straightTarget
  targetExact := rfl
  compatible := by intro state; rfl

end Grass.Tests.CFG.Inheritance
