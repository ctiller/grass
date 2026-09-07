import Grass.Construct.Source.Containment
import Grass.Construct.Source.Elaborate

/-!
# Containment-aware authored-source elaboration

`elaborateContainment` first performs ordinary alpha-normalization and CFG
closure, then rejects duplicate or unattached containment sites on the exact
normalized AST. The result retains both structural and containment certificates;
metadata still contributes no instructions or CFG edges.
-/

namespace Grass.Construct.Source

open Grass.CFG

universe u v w x y

/-- Staged failure from structural alpha closure or containment attachment. -/
inductive ContainmentElaborationError (Terminal : Type v) where
  | alpha (error : AlphaError)
  | containment (error : ContainmentError Terminal)
deriving Repr, DecidableEq

/-- Checked source carrying both structural and containment closure. -/
structure ContainmentElaborated
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Violation : Type x} {Value : Type y} [DecidableEq Terminal]
    (source : PreAlphaAst State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value))
    (model : LabelAlphaModel) where
  elaborated : ElaboratedSource source model
  containment : elaborated.authored.ContainmentWellFormed

namespace ContainmentElaborated

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Violation : Type x} {Value : Type y} [DecidableEq Terminal]
  {source : PreAlphaAst State Terminal Instruction
    (ContainmentAnnotation Terminal Violation Value)}
  {model : LabelAlphaModel}

/-- Exact instruction preservation inherited from structural elaboration. -/
theorem instructionsExact
    (checked : ContainmentElaborated source model) :
    (checked.elaborated.authored.blocks.flatMap fun block => block.body.expand) =
      source.instructions :=
  checked.elaborated.instructionsExact

/-- Erasing checked containment metadata leaves the exact CFG unchanged. -/
theorem erasedGraphExact
    (checked : ContainmentElaborated source model) :
    checked.elaborated.authored.eraseContainment.toGraph =
      checked.elaborated.authored.toGraph :=
  checked.elaborated.authored.eraseContainment_toGraph

/-- Erasing checked metadata leaves every located instruction unchanged. -/
theorem erasedInstructionsExact
    (checked : ContainmentElaborated source model) :
    checked.elaborated.authored.eraseContainment.expandedBlocks =
      checked.elaborated.authored.expandedBlocks :=
  checked.elaborated.authored.eraseContainment_expandedBlocks

end ContainmentElaborated

/-- Perform structural elaboration, then check exact containment attachment. -/
def elaborateContainment
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Violation : Type x} {Value : Type y} [DecidableEq Terminal]
    (source : PreAlphaAst State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value))
    (model : LabelAlphaModel) :
    Except (ContainmentElaborationError Terminal)
      (ContainmentElaborated source model) :=
  match elaborate source model with
  | .error error => .error (.alpha error)
  | .ok elaborated =>
      match checkContainment elaborated.authored with
      | .error error => .error (.containment error)
      | .ok checked =>
          .ok ⟨elaborated, by
            rw [← checked.sourceExact]
            exact checked.valid⟩

end Grass.Construct.Source
