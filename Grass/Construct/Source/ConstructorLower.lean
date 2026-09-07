import Grass.Construct.Lower
import Grass.Construct.Source.ConstructorElaborate

/-!
# Verified constructor-aware source lowering

`VerifiedConstructorElaborated` joins exact constructor-application evidence
with independently supplied block-local semantic verification over the same
alpha-normalized source. `VerifiedConstructorElaborated.lower` reads only the
separate `verified : VerifiedAst` field; constructor identity and exact body
evidence do not construct that field.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x y

/-- Constructor-certified elaboration plus semantic verification of its exact AST. -/
structure VerifiedConstructorElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (source : PreAlphaConstructorSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) where
  constructors : CertifiedConstructorElaborated source model
  verified : VerifiedAst semantics effectModel
    (source.authored.alphaNormalize model)

namespace VerifiedConstructorElaborated

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Effect : Type y}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {source : PreAlphaConstructorSource State Terminal Instruction Annotation
    Effect semantics effectModel}
  {model : LabelAlphaModel}

/-- Total lowering uses only the separately supplied semantic certificate. -/
def lower (checked : VerifiedConstructorElaborated source model) :
    LoweredProgram State Terminal Instruction :=
  checked.verified.lower

/-- Lowering retains exactly the alpha-normalized CFG. -/
@[simp] theorem lower_graph
    (checked : VerifiedConstructorElaborated source model) :
    checked.lower.graph = (source.authored.alphaNormalize model).toGraph := rfl

/-- Lowering locations are exactly the normalized authored locations. -/
theorem lower_items_exact
    (checked : VerifiedConstructorElaborated source model) :
    checked.lower.items =
      (source.authored.alphaNormalize model).loweredItems := rfl

/-- Lowered instructions equal the original pre-alpha authored instructions. -/
theorem lower_instructions_exact
    (checked : VerifiedConstructorElaborated source model) :
    checked.lower.items.map LoweredInstruction.instruction =
      source.authored.instructions := by
  change checked.verified.lower.items.map LoweredInstruction.instruction =
    source.authored.instructions
  rw [checked.verified.lower_instructions_exact]
  exact source.authored.alphaNormalize_instructions model

/-- Exact typed constructor applications remain available after lowering. -/
theorem constructorApplicationsExact
    (checked : VerifiedConstructorElaborated source model) :
    (source.normalized model).Exact :=
  checked.constructors.exact

/-- The constructor and semantic sides refer to one exact normalized AST. -/
theorem constructorAstExact
    (checked : VerifiedConstructorElaborated source model) :
    checked.constructors.checked.elaborated.authored =
      source.authored.alphaNormalize model :=
  checked.constructors.checked.elaborated.authoredExact

end VerifiedConstructorElaborated

end Grass.Construct.Source
