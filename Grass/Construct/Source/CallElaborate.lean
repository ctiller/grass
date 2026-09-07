import Grass.Construct.Source.CallClosure
import Grass.Construct.Source.Elaborate

/-!
# Call-aware authored-source elaboration

`elaborateCalls` alpha-normalizes and structurally validates an authored source
before checking call attachment and return routing on that exact normalized AST.
`CertifiedCallElaborated` separately carries proof-bearing equality between each
containing block contract and its derived call contract.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x

/-- Pre-alpha authored source with its exact instruction-to-call projection. -/
structure PreAlphaCallSource (State : Type u) (Terminal : Type v)
    (Instruction : Type w) (Annotation : Type x) where
  authored : PreAlphaAst State Terminal Instruction Annotation
  callModel : ManifestModel Instruction (CallSite State Terminal)

namespace PreAlphaCallSource

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Exact normalized call source selected by one alpha model. -/
def normalized
    (source : PreAlphaCallSource State Terminal Instruction Annotation)
    (model : LabelAlphaModel) :
    AuthoredCallSource State Terminal Instruction Annotation :=
  ⟨source.authored.alphaNormalize model, source.callModel⟩

end PreAlphaCallSource

/-- Successful structural elaboration and call closure on one normalized AST. -/
structure CallElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} [DecidableEq Terminal]
    (source : PreAlphaCallSource State Terminal Instruction Annotation)
    (model : LabelAlphaModel) : Type (max u v w x) where
  elaborated : ElaboratedSource source.authored model
  calls : CheckedAuthoredCallSource (source.normalized model)

namespace CallElaborated

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} [DecidableEq Terminal]
  {source : PreAlphaCallSource State Terminal Instruction Annotation}
  {model : LabelAlphaModel}

/-- Exact instruction preservation inherited from ordinary elaboration. -/
theorem instructionsExact (checked : CallElaborated source model) :
    (checked.elaborated.authored.blocks.flatMap fun block => block.body.expand) =
      source.authored.instructions :=
  checked.elaborated.instructionsExact

/-- The call checker uses exactly the alpha-normalized authored AST. -/
theorem normalizedAstExact (_checked : CallElaborated source model) :
    (source.normalized model).ast = source.authored.alphaNormalize model := rfl

/-- Ordinary elaboration and call closure retain the same normalized AST. -/
theorem elaboratedAstExact (checked : CallElaborated source model) :
    checked.elaborated.authored = (source.normalized model).ast :=
  checked.elaborated.authoredExact

/-- Every derived call occurrence is structurally closed in the normalized AST. -/
theorem unclosed_eq_nil (checked : CallElaborated source model) :
    (source.normalized model).unclosed = [] :=
  (source.normalized model).unclosed_eq_nil checked.calls.valid

/-- Derived call occurrences project exactly to the normalized call manifest. -/
theorem occurrencesExact (_checked : CallElaborated source model) :
    (source.normalized model).occurrences.map LocatedItem.item =
      (source.normalized model).ast.itemManifest source.callModel :=
  (source.normalized model).occurrencesExact

end CallElaborated

/-- Call-aware elaboration with exact block-to-call contract correspondence. -/
structure CertifiedCallElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} [DecidableEq Terminal]
    (source : PreAlphaCallSource State Terminal Instruction Annotation)
    (model : LabelAlphaModel) : Type (max u v w x) where
  checked : CallElaborated source model
  exact : (source.normalized model).Exact

/-- Staged alpha/CFG or authored-call closure failure. -/
inductive CallElaborationError (Terminal : Type v) where
  | alpha (error : AlphaError)
  | calls (error : AuthoredCallError Terminal)
deriving Repr, DecidableEq

/-- Normalize and structurally close source before checking derived call routes. -/
def elaborateCalls
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} [DecidableEq Terminal]
    (source : PreAlphaCallSource State Terminal Instruction Annotation)
    (model : LabelAlphaModel) :
    Except (CallElaborationError Terminal) (CallElaborated source model) :=
  match elaborate source.authored model with
  | .error error => .error (.alpha error)
  | .ok elaborated =>
      match checkAuthoredCalls (source.normalized model) with
      | .error error => .error (.calls error)
      | .ok calls => .ok ⟨elaborated, calls⟩

end Grass.Construct.Source
