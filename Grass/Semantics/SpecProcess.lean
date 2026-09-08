import Grass.Core.Demand
import Grass.Semantics.Observation

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
  admits : Input -> Prop
  observationProjection : ObservationProjection AuditEvent Observation
  accepts : Input -> List Observation -> Prop
  requirements : DemandFamily.{u}
  /-- Audit events whose ordered occurrences carry evidence for each exact
  independent demand. Refinement must not erase these occurrences even when
  the functional observation projection hides them. -/
  evidenceRelevant : RequirementKey -> AuditEvent -> Bool

end Grass
