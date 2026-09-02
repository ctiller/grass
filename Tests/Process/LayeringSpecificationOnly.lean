import Grass.Specification.Boundary

/-!
# The neutral layer, elaborated without Process in scope

This module imports `Grass.Specification.Boundary` and **nothing else**. That
single-line import list is the whole fixture: everything below has to elaborate
with no `Grass.Process` declaration, instance, or notation available.

`Tests/Process/LayeringFixtures.lean` then re-derives the same facts with the
Process layer present and checks they are unchanged. Together they pin both
halves of `agent-bus` disposition `coord1:5`'s acyclicity: the neutral layer
stands alone, and it means the same thing when the consuming layer is loaded.

Do not add an import to this file. Its value is entirely in what it cannot see.
-/

namespace Grass.Process.Tests.LayeringSpecificationOnly

open Grass.Specification

/-- A platform requirement, named in a scope. -/
def win32Handle : RequirementKey :=
  ⟨⟨["Grass", "Platform", "Win32"]⟩, "GetStdHandle"⟩

/-- A one-element requirement set. -/
def oneRequirement : RequirementSet where
  keys := [win32Handle]
  distinct := by simp

theorem demands_win32Handle : oneRequirement.Demands win32Handle := by
  simp [RequirementSet.Demands, oneRequirement]

/-- Scope containment decides without anything Process-side. -/
theorem platform_scope_nests :
    (⟨["Grass"]⟩ : ScopeId).Contains ⟨["Grass", "Platform", "Win32"]⟩ := rfl

/-- A boundary is constructible here, which is the point: it is neutral. -/
def trivialBoundary : DriverBoundary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := Unit
  requirements := oneRequirement

/-- And its requirement delta is monotone here, with no consumer in scope. -/
theorem delta_is_monotone (key : RequirementKey) :
    (trivialBoundary.demandAlso key).requirements.Covers trivialBoundary.requirements :=
  trivialBoundary.demandAlso_covers key

end Grass.Process.Tests.LayeringSpecificationOnly
