import Grass.Specification.Boundary

/-!
# The neutral layer, elaborated without Process in scope

This module imports `Grass.Specification.Boundary` and **nothing else**, and
everything below elaborates with no `Grass.Process` declaration in scope.

An earlier revision said that the single-line import list *was* the fixture.
`g-foundation:46` pointed out that this is a check a human performs and the
build does not: if `Grass/Specification/Boundary.lean` ever acquired a Process
import, this file would still build, because it would simply inherit it. The
positive theorems below cannot detect that — they would elaborate either way.

The `#guard_msgs` pair at the end is the check that fails. Each names a
Process-side declaration and asserts the elaborator cannot find it, so an import
arriving anywhere under `Grass.Specification` breaks this file rather than
passing unnoticed.

The check is necessarily per-name and not per-namespace: Lean has no way to
assert that a namespace is empty, so a guard catches an import exactly when that
import transitively provides the guarded name. `ProcessSpec` is
`Grass/Process/Spec.lean`'s and sits under most of the layer, and
`LogicalNominal` is `Grass/Process/Nominal.lean`'s, which `Spec.lean` does not
import — so the two together cover both sides of the Process tree's fork rather
than one path through it. Both were checked against a scratch module that does
import them, so neither guard is vacuous.

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

/-! ## The Process layer is not in scope, and the build says so

`g-foundation:46`: everything above would elaborate whether or not
`Grass.Specification` transitively imported `Grass.Process`, so the positive
theorems cannot detect the edge this file exists to forbid. These can. If any
module under `Grass/Specification` acquires a Process import, these names start
resolving and the guards stop matching.

See the module note on why this is two guards and on what per-name checking can
and cannot catch.
-/

/--
error: Unknown identifier `Grass.Process.ProcessSpec`
-/
#guard_msgs in
example := Grass.Process.ProcessSpec

/--
error: Unknown identifier `Grass.Process.LogicalNominal`
-/
#guard_msgs in
example := Grass.Process.LogicalNominal

end Grass.Process.Tests.LayeringSpecificationOnly
