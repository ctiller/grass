import Grass.CFG.Loop
import Grass.Construct.Fragment.Manifest
import Grass.Construct.Source.Ast

/-!
# Authored source discovery

`Ast.discover` derives the graph, joins, cyclic regions, and generic instruction
occurrences from one authored AST.  `Ast.discoveredItems_exact` ties the located
occurrences to the occurrence-exact `Ast.itemManifest`; repeated projected items
remain repeated and retain their containing block and structural source origin.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x y

/-- One projected instruction item with its exact authored location. -/
structure LocatedItem (Item : Type y) where
  block : BlockId
  origin : SourceOrigin
  projectedIndex : Nat
  item : Item
deriving Repr, DecidableEq

/-- Complete structural discovery snapshot for one generic projected item type. -/
structure Discovery (State : Type u) (Terminal : Type v) (Item : Type y) where
  graph : CFG.Graph State Terminal
  joins : List (CFG.Graph.JoinDemand)
  loops : List (CFG.Graph.LoopDemand)
  items : List (LocatedItem Item)

namespace Ast

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Item : Type y}

private def locateItems (block : BlockId) (origin : SourceOrigin) :
    Nat → List Item → List (LocatedItem Item)
  | _, [] => []
  | index, item :: rest =>
      ⟨block, origin, index, item⟩ :: locateItems block origin (index + 1) rest

private theorem map_locateItems (block : BlockId) (origin : SourceOrigin)
    (index : Nat) (items : List Item) :
    (locateItems block origin index items).map LocatedItem.item = items := by
  induction items generalizing index with
  | nil => rfl
  | cons item rest ih => simp [locateItems, ih]

/-- Occurrence-exact item manifest across blocks in authored order. -/
def itemManifest (source : Ast State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) : List Item :=
  source.blocks.flatMap fun block => block.body.manifest model

/-- Located projected items across blocks and instructions in authored order. -/
def discoverItems (source : Ast State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) : List (LocatedItem Item) :=
  source.blocks.flatMap fun block =>
    block.body.expandLocated.flatMap fun located =>
      locateItems block.cfg.id located.origin 0 (model.project located.instruction)

private theorem discoverBlockItems_exact
    (block : Block State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) :
    (block.body.expandLocated.flatMap fun located =>
      locateItems block.cfg.id located.origin 0
        (model.project located.instruction)).map LocatedItem.item =
      block.body.manifest model := by
  unfold Fragment.Source.manifest
  rw [Fragment.Source.expand_eq_map_located]
  simp only [List.flatMap_map]
  induction block.body.expandLocated with
  | nil => rfl
  | cons located rest ih =>
      simp [map_locateItems, ih]

private theorem discoverBlocksItems_exact
    (blocks : List (Block State Terminal Instruction Annotation))
    (model : ManifestModel Instruction Item) :
    (blocks.flatMap fun block =>
      block.body.expandLocated.flatMap fun located =>
        locateItems block.cfg.id located.origin 0
          (model.project located.instruction)).map LocatedItem.item =
      blocks.flatMap fun block => block.body.manifest model := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.flatMap_cons, List.map_append]
      rw [discoverBlockItems_exact block model, ih]

/-- Located discovery projects exactly to the occurrence manifest. -/
theorem discoveredItems_exact
    (source : Ast State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) :
    (source.discoverItems model).map LocatedItem.item = source.itemManifest model := by
  exact discoverBlocksItems_exact source.blocks model

/-- Derive all structural views from one authored AST. -/
def discover (source : Ast State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) : Discovery State Terminal Item where
  graph := source.toGraph
  joins := source.toGraph.discoverJoins
  loops := source.toGraph.discoverLoops
  items := source.discoverItems model

@[simp] theorem discover_graph
    (source : Ast State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) :
    (source.discover model).graph = source.toGraph := rfl

@[simp] theorem discover_joins
    (source : Ast State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) :
    (source.discover model).joins = source.toGraph.discoverJoins := rfl

@[simp] theorem discover_loops
    (source : Ast State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) :
    (source.discover model).loops = source.toGraph.discoverLoops := rfl

end Ast

end Grass.Construct.Source
