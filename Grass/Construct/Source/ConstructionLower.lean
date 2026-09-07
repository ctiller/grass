import Grass.Construct.Lower
import Grass.Construct.Source.ConstructionElaborate

/-!
# Verified unified construction lowering

`VerifiedConstructionElaborated` combines the unified constructor/call
certificate with independently supplied block-local semantic verification over
the same alpha-normalized AST. `VerifiedConstructionElaborated.lower` consumes
only that `VerifiedAst`; constructor and call certificates remain inspectable
provenance rather than being promoted into instruction semantics.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x y

/-- Unified construction certification plus semantic verification of its AST. -/
structure VerifiedConstructionElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    [DecidableEq Terminal]
    (source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) : Type (max u v w x y) where
  construction : CertifiedConstructionElaborated source model
  verified : VerifiedAst semantics effectModel
    (source.authored.alphaNormalize model)

namespace VerifiedConstructionElaborated

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Effect : Type y}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  [DecidableEq Terminal]
  {source : PreAlphaConstructionSource State Terminal Instruction Annotation
    Effect semantics effectModel}
  {model : LabelAlphaModel}

/-- Total lowering uses only the separately supplied semantic certificate. -/
def lower (checked : VerifiedConstructionElaborated source model) :
    LoweredProgram State Terminal Instruction :=
  checked.verified.lower

/-- Lowering retains exactly the unified alpha-normalized CFG. -/
@[simp] theorem lower_graph
    (checked : VerifiedConstructionElaborated source model) :
    checked.lower.graph = (source.authored.alphaNormalize model).toGraph := rfl

/-- Lowering locations are exactly the normalized authored locations. -/
theorem lower_items_exact
    (checked : VerifiedConstructionElaborated source model) :
    checked.lower.items =
      (source.authored.alphaNormalize model).loweredItems := rfl

/-- Lowered instructions equal the original pre-alpha authored instructions. -/
theorem lower_instructions_exact
    (checked : VerifiedConstructionElaborated source model) :
    checked.lower.items.map LoweredInstruction.instruction =
      source.authored.instructions := by
  change checked.verified.lower.items.map LoweredInstruction.instruction =
    source.authored.instructions
  rw [checked.verified.lower_instructions_exact]
  exact source.authored.alphaNormalize_instructions model

/-- Exact typed constructor applications remain available after lowering. -/
theorem constructorApplicationsExact
    (checked : VerifiedConstructionElaborated source model) :
    (source.constructorSource.normalized model).Exact :=
  checked.construction.constructorApplications

/-- Exact block-to-call contract correspondence remains available after lowering. -/
theorem callContractsExact
    (checked : VerifiedConstructionElaborated source model) :
    (source.callSource.normalized model).Exact :=
  checked.construction.callContracts

/-- The unified executable gates and semantic verification share one exact AST. -/
theorem constructionAstExact
    (checked : VerifiedConstructionElaborated source model) :
    checked.construction.checked.elaborated.authored =
      source.authored.alphaNormalize model :=
  checked.construction.checked.elaborated.authoredExact

end VerifiedConstructionElaborated

end Grass.Construct.Source
