import Grass.Construct.Source.CallElaborate
import Grass.Construct.Source.ConstructorElaborate

/-!
# Unified construction-source elaboration

`elaborateConstruction` performs alpha/CFG validation, constructor closure,
and authored-call routing in that order over one exact normalized AST. The
`ConstructionElaborated` fields share one `model` index, and
`ConstructionElaborated.astExact` exposes their common AST. Exact constructor
applications and predicate-bearing call-contract equality remain separate
fields of `CertifiedConstructionElaborated`.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x y

/-- Pre-alpha source with exact constructor and call-projection inputs. -/
structure PreAlphaConstructionSource (State : Type u) (Terminal : Type v)
    (Instruction : Type w) (Annotation : Type x) (Effect : Type y)
    (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  authored : PreAlphaAst State Terminal Instruction Annotation
  closure : ConstructorClosure Instruction State Effect semantics effectModel
  checkedClosure : CheckedConstructorClosure closure
  callModel : ManifestModel Instruction (CallSite State Terminal)

namespace PreAlphaConstructionSource

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Effect : Type y}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}

/-- Constructor view retaining the exact authored source and closure input. -/
def constructorSource
    (source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel) :
    PreAlphaConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel :=
  ⟨source.authored, source.closure, source.checkedClosure⟩

/-- Call view retaining the exact authored source and call projection. -/
def callSource
    (source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel) :
    PreAlphaCallSource State Terminal Instruction Annotation :=
  ⟨source.authored, source.callModel⟩

end PreAlphaConstructionSource

/-- All executable authored construction gates over one normalized source. -/
structure ConstructionElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    [DecidableEq Terminal]
    (source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) : Type (max u v w x y) where
  elaborated : ElaboratedSource source.authored model
  constructors : CheckedConstructorSource
    (source.constructorSource.normalized model)
  calls : CheckedAuthoredCallSource (source.callSource.normalized model)

namespace ConstructionElaborated

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Effect : Type y}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  [DecidableEq Terminal]
  {source : PreAlphaConstructionSource State Terminal Instruction Annotation
    Effect semantics effectModel}
  {model : LabelAlphaModel}

/-- All three gates retain exactly the alpha-normalized authored AST. -/
theorem astExact (checked : ConstructionElaborated source model) :
    checked.elaborated.authored =
        (source.constructorSource.normalized model).ast ∧
      checked.elaborated.authored =
        (source.callSource.normalized model).ast :=
  ⟨checked.elaborated.authoredExact, checked.elaborated.authoredExact⟩

/-- Exact pre-alpha instruction preservation inherited from elaboration. -/
theorem instructionsExact (checked : ConstructionElaborated source model) :
    (checked.elaborated.authored.blocks.flatMap fun block => block.body.expand) =
      source.authored.instructions :=
  checked.elaborated.instructionsExact

/-- Every structural constructor occurrence resolves in the supplied closure. -/
theorem unresolvedConstructors_eq_nil
    (checked : ConstructionElaborated source model) :
    (source.constructorSource.normalized model).unresolved = [] :=
  checked.constructors.valid.2

/-- Every derived authored call is attached and routed by its containing block. -/
theorem unclosedCalls_eq_nil (checked : ConstructionElaborated source model) :
    (source.callSource.normalized model).unclosed = [] :=
  (source.callSource.normalized model).unclosed_eq_nil checked.calls.valid

end ConstructionElaborated

/-- Unified elaboration with exact constructor and call-contract certificates. -/
structure CertifiedConstructionElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    [DecidableEq Terminal]
    (source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) : Type (max u v w x y) where
  checked : ConstructionElaborated source model
  constructorApplications : (source.constructorSource.normalized model).Exact
  callContracts : (source.callSource.normalized model).Exact

/-- Exact stage at which unified construction elaboration failed. -/
inductive ConstructionElaborationError (Terminal : Type v) where
  | alpha (error : AlphaError)
  | constructors (error : ConstructorSourceError)
  | calls (error : AuthoredCallError Terminal)
deriving Repr, DecidableEq

/-- Run alpha/CFG, constructor, then call closure over one normalized AST. -/
def elaborateConstruction
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    [DecidableEq Terminal]
    (source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel)
    (model : LabelAlphaModel) :
    Except (ConstructionElaborationError Terminal)
      (ConstructionElaborated source model) :=
  match elaborate source.authored model with
  | .error error => .error (.alpha error)
  | .ok elaborated =>
      match checkConstructorSource (source.constructorSource.normalized model) with
      | .error error => .error (.constructors error)
      | .ok constructors =>
          match checkAuthoredCalls (source.callSource.normalized model) with
          | .error error => .error (.calls error)
          | .ok calls => .ok ⟨elaborated, constructors, calls⟩

end Grass.Construct.Source
