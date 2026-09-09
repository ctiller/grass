import Grass.Console.Captured
import Grass.Console.TargetProjection

/-! Target selection consumes the exact captured context. It does not re-read
resource capabilities, rebuild a request, or discharge its independent demands. -/

namespace Grass.Console

open Specification

variable {R Outcome Status : Type} [model : Resource.ResourceModel R] {resources : R}

/-- Retain the exact captured suite and its model/value indices. There is no
replacement request, resource snapshot, or demand context field. -/
structure CapturedTargetProjection (spec : CapturedSpecification resources Outcome) (Status : Type) where
  target : TargetProjection spec.context.request Status

namespace CapturedTargetProjection

variable {spec : CapturedSpecification resources Outcome}

def system (projection : CapturedTargetProjection spec Status) := projection.target.system

abbrev Complete (projection : CapturedTargetProjection spec Status) := projection.target.Complete

def resourceSemantics (_projection : CapturedTargetProjection spec Status) :
    ConsoleResourceSnapshot model resources := spec.context.resourceSemantics

end CapturedTargetProjection

namespace CapturedSpecification

def project (spec : CapturedSpecification resources Outcome) (rendering : LineRendering)
    (encodeOutcome : Outcome → Status) : CapturedTargetProjection spec Status :=
  ⟨⟨rendering, encodeOutcome⟩⟩

theorem project_system (spec : CapturedSpecification resources Outcome) (rendering : LineRendering)
    (encodeOutcome : Outcome → Status) :
    (spec.project rendering encodeOutcome).system = spec.system rendering := rfl

theorem project_complete (spec : CapturedSpecification resources Outcome) (rendering : LineRendering)
    (encodeOutcome : Outcome → Status) :
    (spec.project rendering encodeOutcome).Complete = spec.Complete rendering := rfl

/-- Appending liveness demands does not filter target histories. -/
theorem project_withLiveness (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) (rendering : LineRendering) (encodeOutcome : Outcome → Status) :
    ((spec.withLiveness fragment).project rendering encodeOutcome).Complete =
      (spec.project rendering encodeOutcome).Complete := rfl

end CapturedSpecification
end Grass.Console
