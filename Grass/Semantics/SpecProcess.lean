import Grass.Core.Demand
import Grass.Semantics.Observation

/-!
# Minimal captured specification boundary

This is the foundation-level root consumed by certificates. Domain DSLs and
resource libraries construct values of this type; they do not extend the
verified gate with alternate correctness routes.

`Grass.SpecRoot` was named `Grass.SpecProcess` before the resource-indexed
authoring root (`Grass.SpecProcess {R} [ResourceModel R] (resources : R)`,
`Grass/Spec/Root.lean`) took that name. Every certificate tier still consumes
exactly this unindexed record; the authoring root's `SpecProcess.root`
recomputes one of these from a resource-indexed specification.
-/

namespace Grass

universe u

/-- One exact portable behavior and its independently keyed demands. -/
structure SpecRoot where
  Input : Type u
  AuditEvent : Type u
  Observation : Type u
  admits : Input -> Prop
  observationProjection : ObservationProjection AuditEvent Observation
  accepts : Input -> List Observation -> Prop
  requirements : DemandFamily.{u}

end Grass
