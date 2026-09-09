import Grass.Console.Contract
import Grass.Console.TargetProjection

/-! Projection captures one view of the sole specification root. Component
histories remain distinct from the whole program's reporting/observed phases.
The stored view supplies the original snapshot and exact interpretation/input
correspondence; later use neither re-queries resources nor rebuilds a contract.
-/

namespace Grass.Console

open Specification

variable {R Status : Type} [model : Resource.ResourceModel R] {resources : R}

/-- Keep the whole root (including its liveness fragments), exact captured view,
and target data. There is no independent replacement specification or outcome type. -/
structure CapturedTargetProjection (spec : SpecProcess resources) (Status : Type) where
  view : ContractView spec.contract
  target : TargetProjection view.request Status

namespace CapturedTargetProjection

variable {spec : SpecProcess resources}

def componentSystem (projection : CapturedTargetProjection spec Status) :=
  projection.target.componentSystem

abbrev componentComplete (projection : CapturedTargetProjection spec Status) :=
  projection.target.componentComplete

def resourceSemantics (projection : CapturedTargetProjection spec Status) :
    ConsoleResourceSnapshot model resources := projection.view.snapshot

/-- Whole-program meaning comes only from the exact root at the captured
view's selected interpretation and input. It is not the component system. -/
def wholeModel (projection : CapturedTargetProjection spec Status) : BehaviorModel spec.Outcome :=
  spec.denotation (projection.view.interpret projection.target.rendering) projection.view.input

theorem wholeModel_exact (projection : CapturedTargetProjection spec Status) :
    projection.wholeModel = ObservedBehavior.model projection.view.request projection.target.rendering := by
  exact (projection.view.model_exact
    (projection.view.interpret projection.target.rendering) projection.view.input).trans
    (congrArg (ObservedBehavior.model projection.view.request)
      (projection.view.rendering_interpret projection.target.rendering))

/-- All root inputs are covered by the captured view; no friendly input is selected. -/
theorem wholeModel_input_exact (projection : CapturedTargetProjection spec Status) (input : spec.Input) :
    spec.denotation (projection.view.interpret projection.target.rendering) input = projection.wholeModel := by
  rw [projection.view.input_unique input]
  rfl

end CapturedTargetProjection
end Grass.Console

namespace Grass.SpecProcess

open Console Specification

variable {R Status : Type} [Resource.ResourceModel R] {resources : R}

/-- Select the view once at construction; the returned projection stores it. -/
def project (spec : SpecProcess resources)
    (rendering : LineRendering) (encodeOutcome : spec.Outcome → Status)
    (view : ContractView spec.contract := by apply Console.writeLineView) :
    CapturedTargetProjection spec Status := ⟨view, ⟨rendering, encodeOutcome⟩⟩

theorem project_componentSystem (spec : SpecProcess resources) [view : ContractView spec.contract]
    (rendering : LineRendering) (encodeOutcome : spec.Outcome → Status) :
    (spec.project rendering encodeOutcome view).componentSystem = view.request.system rendering := rfl

theorem project_componentComplete (spec : SpecProcess resources) [view : ContractView spec.contract]
    (rendering : LineRendering) (encodeOutcome : spec.Outcome → Status) :
    (spec.project rendering encodeOutcome view).componentComplete = view.request.Complete rendering := rfl

/-- Appending an author theorem demand leaves component histories unchanged,
while the projection type still retains the exact appended root. -/
theorem project_withLiveness (spec : SpecProcess resources) [view : ContractView spec.contract]
    (fragment : LivenessContract) (rendering : LineRendering) (encodeOutcome : spec.Outcome → Status) :
    ((spec.withLiveness fragment).project (view := view) rendering encodeOutcome).componentComplete =
      (spec.project rendering encodeOutcome view).componentComplete := rfl

end Grass.SpecProcess
