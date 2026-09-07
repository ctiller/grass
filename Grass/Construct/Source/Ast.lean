import Grass.CFG.Graph
import Grass.Construct.Fragment.Source

/-!
# Authored source values

An authored program stores each block's CFG declaration beside its one
hierarchical instruction source.  `Ast.toGraph` and `Ast.expandedBlocks` are
projections of that value; authors do not maintain parallel graph or flattened
instruction manifests.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x

/-- One authored block, including review-only annotations that do not affect
its CFG identity or exact instruction expansion. -/
structure Block (State : Type u) (Terminal : Type v) (Instruction : Type w)
    (Annotation : Type x) where
  cfg : CFG.Block State Terminal
  body : Fragment.Source Instruction
  annotations : List Annotation

/-- Stable term-level authored CFG surface. -/
structure Ast (State : Type u) (Terminal : Type v) (Instruction : Type w)
    (Annotation : Type x) where
  entry : BlockId
  blocks : List (Block State Terminal Instruction Annotation)

namespace Ast

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- The exact CFG projection of authored blocks, in source order. -/
def toGraph (source : Ast State Terminal Instruction Annotation) :
    CFG.Graph State Terminal where
  entry := source.entry
  blocks := source.blocks.map Block.cfg

/-- Authored block identities in source order. -/
def blockIds (source : Ast State Terminal Instruction Annotation) : List BlockId :=
  source.blocks.map fun block => block.cfg.id

/-- Find an authored block by stable CFG identity. -/
def findBlock? (source : Ast State Terminal Instruction Annotation) (id : BlockId) :
    Option (Block State Terminal Instruction Annotation) :=
  source.blocks.find? fun block => block.cfg.id == id

/-- Located instruction expansions paired with their containing block identity. -/
def expandedBlocks (source : Ast State Terminal Instruction Annotation) :
    List (BlockId × List (LocatedInstruction Instruction)) :=
  source.blocks.map fun block => (block.cfg.id, block.body.expandLocated)

/-- Total instruction count across authored blocks. -/
def instructionCount (source : Ast State Terminal Instruction Annotation) : Nat :=
  (source.blocks.map fun block => block.body.instructionCount).sum

/-- Structural closure is exactly closure of the graph projected from the same
authored value. -/
def WellFormed (source : Ast State Terminal Instruction Annotation) : Prop :=
  source.toGraph.WellFormed

instance (source : Ast State Terminal Instruction Annotation) :
    Decidable source.WellFormed :=
  inferInstanceAs (Decidable source.toGraph.WellFormed)

@[simp] theorem toGraph_blockIds (source : Ast State Terminal Instruction Annotation) :
    source.toGraph.blockIds = source.blockIds := by
  simp [toGraph, blockIds, CFG.Graph.blockIds]

@[simp] theorem toGraph_entry (source : Ast State Terminal Instruction Annotation) :
    source.toGraph.entry = source.entry := rfl

/-- A successful authored lookup projects to the same CFG block lookup. -/
theorem findBlock?_map_cfg (source : Ast State Terminal Instruction Annotation)
    (id : BlockId) :
    (source.findBlock? id).map Block.cfg = source.toGraph.findBlock? id := by
  simp only [findBlock?, toGraph, CFG.Graph.findBlock?, List.find?_map]
  rfl

end Ast

end Grass.Construct.Source
