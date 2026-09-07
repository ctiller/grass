import Grass.Construct.Source.Ast

/-!
# Authored source fixtures

Fixtures pin the single-source projection of block identity, CFG structure,
annotations, hierarchical instruction locations, and instruction counts.
-/

namespace Grass.Tests.Construct.SourceAst

open Grass Grass.CFG Grass.Construct.Fragment

def blockId (name : String) : BlockId := ⟨⟨"test.source", name⟩⟩
def exitTag (name : String) : ExitTag := ⟨⟨"test.source", name⟩⟩
def fragmentId (name : String) : FragmentId := ⟨⟨"test.source", name⟩⟩

def contract : BlockContract Nat where
  requires := fun _ => True
  exits := [⟨exitTag "done", fun _ => True⟩]

def first : Grass.Construct.Source.Block Nat String Nat String where
  cfg := ⟨blockId "first", contract, [⟨exitTag "done", .block (blockId "second")⟩]⟩
  body := .generated (fragmentId "pair") (.literal [1, 2])
  annotations := ["reviewed"]

def second : Grass.Construct.Source.Block Nat String Nat String where
  cfg := ⟨blockId "second", contract, [⟨exitTag "done", .terminal "return"⟩]⟩
  body := .sequence [.literal [3], .literal [4, 5]]
  annotations := []

def source : Grass.Construct.Source.Ast Nat String Nat String where
  entry := blockId "first"
  blocks := [first, second]

example : source.blockIds = [blockId "first", blockId "second"] := by decide
example : source.toGraph.blocks = [first.cfg, second.cfg] := by rfl
example : source.toGraph.WellFormed := by native_decide
example : source.WellFormed := by native_decide
example : (source.findBlock? (blockId "first")).map
    Grass.Construct.Source.Block.annotations =
    some ["reviewed"] := by native_decide

example : source.expandedBlocks.map (fun entry => (entry.1,
    entry.2.map LocatedInstruction.instruction)) =
    [(blockId "first", [1, 2]), (blockId "second", [3, 4, 5])] := by native_decide

example : source.instructionCount = 5 := by native_decide

example : (source.findBlock? (blockId "first")).map
    Grass.Construct.Source.Block.cfg =
    source.toGraph.findBlock? (blockId "first") :=
  Grass.Construct.Source.Ast.findBlock?_map_cfg source (blockId "first")

end Grass.Tests.Construct.SourceAst
