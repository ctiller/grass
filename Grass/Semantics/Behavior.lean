import Grass.Semantics.Observation

/-!
# Portable behavior contracts

The behavior of a specification and the theorem demands attached to that
behavior have different owners in the verification pipeline.  A
`BehaviorContract` contains only the admitted inputs and their observable
meaning.  `SpecProcess` adds its independently keyed `DemandFamily` in
`Grass.Semantics.SpecProcess`.

Keeping this boundary explicit lets Refinement compare a selected network
trace with precious behavior without silently identifying or discarding the
requirements that still need certificates.
-/

namespace Grass

universe u

/-- One portable input/observation relation, independent of certificate demands. -/
structure BehaviorContract where
  /-- Inputs whose behavior is specified. -/
  Input : Type u
  /-- Events retained by the complete audit trace. -/
  AuditEvent : Type u
  /-- Observations exposed by this contract. -/
  Observation : Type u
  /-- The admitted input domain. -/
  admits : Input → Prop
  /-- Projection from the audit trace to contract observations. -/
  observationProjection : ObservationProjection AuditEvent Observation
  /-- The accepted observation traces for an admitted input. -/
  accepts : Input → List Observation → Prop

end Grass
