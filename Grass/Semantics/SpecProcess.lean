import Grass.Core.Demand
import Grass.Semantics.Behavior

/-!
# Minimal captured specification boundary

This is the foundation-level root consumed by certificates. Domain DSLs and
resource libraries construct values of this type; they do not extend the
verified gate with alternate correctness routes.
-/

namespace Grass

universe u

/-- One exact portable behavior and its independently keyed demands. -/
structure SpecProcess where
  Input : Type u
  AuditEvent : Type u
  Observation : Type u
  admits : Input → Prop
  observationProjection : ObservationProjection AuditEvent Observation
  accepts : Input → List Observation → Prop
  requirements : DemandFamily.{u}

namespace SpecProcess

/-- Forget certificate demands and expose only the precious behavior. -/
def contract (spec : SpecProcess) : BehaviorContract :=
  { Input := spec.Input
    AuditEvent := spec.AuditEvent
    Observation := spec.Observation
    admits := spec.admits
    observationProjection := spec.observationProjection
    accepts := spec.accepts }

@[simp] theorem contract_input (spec : SpecProcess) :
    spec.contract.Input = spec.Input := rfl

@[simp] theorem contract_auditEvent (spec : SpecProcess) :
    spec.contract.AuditEvent = spec.AuditEvent := rfl

@[simp] theorem contract_observation (spec : SpecProcess) :
    spec.contract.Observation = spec.Observation := rfl

end SpecProcess

end Grass
