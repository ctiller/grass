import Grass.Construct.Source.ConstructorClosure
import Grass.Construct.Source.Elaborate

/-!
# Constructor-aware authored-source elaboration

`elaborateConstructors` composes alpha-normalization and ordinary structural
elaboration with constructor-closure checking against one exact dependent input.
Alpha/CFG failures are reported before constructor failures. Exact correspondence
between generated bodies and typed constructor applications remains a separate
proof-bearing certificate rather than being inferred from matching identities.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x y

/-- Pre-alpha authored source with its exact checked constructor input. -/
structure PreAlphaConstructorSource (State : Type u) (Terminal : Type v)
    (Instruction : Type w) (Annotation : Type x) (Effect : Type y)
    (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  authored : PreAlphaAst State Terminal Instruction Annotation
  closure : ConstructorClosure Instruction State Effect semantics effectModel
  checkedClosure : CheckedConstructorClosure closure

namespace PreAlphaConstructorSource

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Effect : Type y}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}

/-- Exact normalized constructor source selected by one alpha model. -/
def normalized
    (source : PreAlphaConstructorSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) :
    ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel :=
  ⟨source.authored.alphaNormalize model, source.closure, source.checkedClosure⟩

end PreAlphaConstructorSource

/-- Successful structural elaboration plus constructor closure on the same source. -/
structure ConstructorElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (source : PreAlphaConstructorSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) where
  elaborated : ElaboratedSource source.authored model
  constructors : CheckedConstructorSource (source.normalized model)

namespace ConstructorElaborated

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Effect : Type y}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {source : PreAlphaConstructorSource State Terminal Instruction Annotation
    Effect semantics effectModel}
  {model : LabelAlphaModel}

/-- Exact instruction preservation inherited from ordinary elaboration. -/
theorem instructionsExact (checked : ConstructorElaborated source model) :
    (checked.elaborated.authored.blocks.flatMap fun block => block.body.expand) =
      source.authored.instructions :=
  checked.elaborated.instructionsExact

/-- The constructor checker uses exactly the alpha-normalized authored AST. -/
theorem normalizedAstExact (_checked : ConstructorElaborated source model) :
    (source.normalized model).ast = source.authored.alphaNormalize model := rfl

/-- Ordinary elaboration and constructor closure retain the same normalized AST. -/
theorem elaboratedAstExact (checked : ConstructorElaborated source model) :
    checked.elaborated.authored = (source.normalized model).ast :=
  checked.elaborated.authoredExact

/-- Every structural constructor occurrence resolves in the selected input. -/
theorem unresolved_eq_nil (checked : ConstructorElaborated source model) :
    (source.normalized model).unresolved = [] :=
  checked.constructors.valid.2

end ConstructorElaborated

/--
Constructor-aware elaboration with exact typed-application correspondence.

The executable elaborator returns `ConstructorElaborated`; a frontend or backend
that authored the typed applications separately supplies this exactness proof.
-/
structure CertifiedConstructorElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (source : PreAlphaConstructorSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) where
  checked : ConstructorElaborated source model
  exact : (source.normalized model).Exact

/-- Staged alpha/CFG or constructor-closure elaboration failure. -/
inductive ConstructorElaborationError where
  | alpha (error : AlphaError)
  | constructors (error : ConstructorSourceError)
deriving Repr, DecidableEq

/-- Normalize and structurally close source before checking constructor closure. -/
def elaborateConstructors
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (source : PreAlphaConstructorSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) :
    Except ConstructorElaborationError (ConstructorElaborated source model) :=
  match elaborate source.authored model with
  | .error error => .error (.alpha error)
  | .ok elaborated =>
      match checkConstructorSource (source.normalized model) with
      | .error error => .error (.constructors error)
      | .ok constructors => .ok ⟨elaborated, constructors⟩

end Grass.Construct.Source
