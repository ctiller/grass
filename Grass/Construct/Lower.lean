import Grass.Construct.Fragment.Verified
import Grass.Construct.Source.Ast

/-!
# Checked authored-source lowering

`VerifiedAst` requires one locally correct `VerifiedFragment` for every authored
block and an equality tying that fragment to the block's exact source body.
`VerifiedAst.lower` then returns all instructions with a one-for-one block and
`SourceOrigin` map; no partial result or proof-free promotion is exposed.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Fragment

universe u v w x y z

namespace Source

/-- One lowered instruction with its containing block and exact source origin. -/
structure LoweredInstruction (Instruction : Type w) where
  block : BlockId
  origin : SourceOrigin
  instruction : Instruction
deriving Repr, DecidableEq

/-- Complete checked lowering output. -/
structure LoweredProgram (State : Type u) (Terminal : Type v)
    (Instruction : Type w) where
  graph : CFG.Graph State Terminal
  items : List (LoweredInstruction Instruction)

/-- One authored block tied to its exact locally correct fragment. -/
structure VerifiedBlock {State : Type u} {Terminal : Type v}
    {Instruction : Type w} (Annotation : Type x) {Effect : Type y}
    (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  authored : Block State Terminal Instruction Annotation
  fragment : VerifiedFragment semantics effectModel authored.cfg.contract
  sourceExact : fragment.source = authored.body

/-- Verification evidence aligned one-for-one with one exact authored AST. -/
structure VerifiedAst {State : Type u} {Terminal : Type v}
    {Instruction : Type w} {Annotation : Type x} {Effect : Type y}
    (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect)
    (source : Ast State Terminal Instruction Annotation) where
  structural : source.WellFormed
  blocks : List (VerifiedBlock Annotation semantics effectModel)
  blocksExact : blocks.map VerifiedBlock.authored = source.blocks

namespace Ast

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Total located flattening of an authored AST before its verification
argument is erased into lowering authority. -/
def loweredItems (source : Ast State Terminal Instruction Annotation) :
    List (LoweredInstruction Instruction) :=
  source.blocks.flatMap fun block =>
    block.body.expandLocated.map fun located =>
      ⟨block.cfg.id, located.origin, located.instruction⟩

/-- Flat authored instructions in block order. -/
def instructions (source : Ast State Terminal Instruction Annotation) : List Instruction :=
  source.blocks.flatMap fun block => block.body.expand

/-- Lowering locations project exactly to the authored flat instruction list. -/
theorem loweredItems_exact (source : Ast State Terminal Instruction Annotation) :
    source.loweredItems.map LoweredInstruction.instruction = source.instructions := by
  unfold loweredItems instructions
  induction source.blocks with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_map]
      have headExact :
          block.body.expandLocated.map
            (LoweredInstruction.instruction ∘ fun located =>
              ⟨block.cfg.id, located.origin, located.instruction⟩) =
            block.body.expand := by
        change block.body.expandLocated.map LocatedInstruction.instruction =
          block.body.expand
        exact (Fragment.Source.expand_eq_map_located block.body).symm
      rw [headExact, ih]

end Ast

namespace VerifiedAst

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Effect : Type y}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {source : Ast State Terminal Instruction Annotation}

/-- Checked lowering of the exact AST witnessed by `VerifiedAst`. -/
def lower (_verified : VerifiedAst semantics effectModel source) :
    LoweredProgram State Terminal Instruction where
  graph := source.toGraph
  items := source.loweredItems

@[simp] theorem lower_graph (_verified : VerifiedAst semantics effectModel source) :
    _verified.lower.graph = source.toGraph := rfl

/-- Checked output instructions equal the authored flat expansion exactly. -/
theorem lower_instructions_exact (_verified : VerifiedAst semantics effectModel source) :
    _verified.lower.items.map LoweredInstruction.instruction = source.instructions :=
  source.loweredItems_exact

end VerifiedAst

end Source

end Grass.Construct
