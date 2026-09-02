import Grass.Specification.Boundary
import Tests.Process.LayeringSpecificationOnly
import Tests.Process.M1CorrectFixtures
import Grass.Process.Correct
import Grass.Process.Network.Topology
import Grass.Process.Sequential.Machine

/-!
# The layering the diamond requires

`agent-bus` disposition `coord1:5`, ruling on issue `c-process:4`, requires an
import-cycle fixture alongside the layer move. This is it.

The property to protect is one-directional: **`Grass.Specification` must not
depend on `Grass.Process`.** That is what makes the diamond acyclic, and it is
what the old placement violated — `Boundary.lean` imported `Grass.Process.Spec`
to offer a vocabulary view, so the neutral record depended on the layer that
consumes it.

## What a Lean fixture can and cannot check

It cannot enumerate a module's imports; that is build-graph information, not
environment information. What it *can* do is the thing that actually matters:
force the neutral layer's declarations to elaborate in a context where nothing
from `Grass.Process` is available, so that if someone adds a Process dependency
to `Grass/Specification/*`, this file stops compiling.

`Tests/Process/LayeringSpecificationOnly.lean` is that context — it imports the
neutral layer alone. This module then re-derives the same facts *with* the
Process layer present and checks they are unchanged, which catches the subtler
failure: a `Grass.Specification` declaration that still elaborates standalone
but whose meaning silently depends on a `Grass.Process` instance or default
being in scope.

The structural half — that no file under `Grass/Specification/` contains an
`import Grass.Process` line — is a one-line grep and belongs in CI, not in Lean.
It is recorded in `docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2 as an obligation on
whoever owns the build gate.
-/

namespace Grass.Process.Tests

open Grass.Specification

/-! ## The neutral layer means the same thing with Process in scope -/

/-- A requirement key built here is the one built in the Process-free context. -/
theorem requirementKey_stable :
    (⟨⟨["Grass", "Platform", "Win32"]⟩, "GetStdHandle"⟩ : RequirementKey) =
      LayeringSpecificationOnly.win32Handle := rfl

/-- And so is a requirement set, including its duplicate-freedom proof. -/
theorem requirementSet_stable :
    LayeringSpecificationOnly.oneRequirement.keys =
      [LayeringSpecificationOnly.win32Handle] := rfl

/-- Requirement coverage is decided identically on both sides. -/
theorem covers_stable :
    LayeringSpecificationOnly.oneRequirement.Demands
      LayeringSpecificationOnly.win32Handle :=
  LayeringSpecificationOnly.demands_win32Handle

/--
The monotone delta is the same operation on both sides.

`demandAlso` is the one place the neutral layer has real behaviour rather than
just shape, so it is the one worth pinning: if it were ever to consult something
Process-side, this equation would break.
-/
theorem demandAlso_stable (boundary : DriverBoundary.{0}) (key : RequirementKey) :
    (boundary.demandAlso key).requirements.Demands key :=
  boundary.demandAlso_demands key

/-! ## Process depends on Specification, and that direction is fine

The other arm of the diamond is exercised by construction: this module imports
both layers and uses `DriverBoundary` inside Process-side definitions. If the
dependency were ever inverted, `Grass.Process.ProtocolExposesBoundary` could not
mention `DriverBoundary` at all.
-/

/-- A boundary with no requirements, used below. -/
@[reducible] def emptyBoundary : DriverBoundary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := Unit
  requirements := RequirementSet.empty

/--
A Process-side structure over a neutral-layer boundary.

This is the permitted direction. It elaborates only because `Grass.Process` may
import `Grass.Specification`; the fixture above is what stops the reverse.
-/
@[reducible] def emptyExposure :
    ProtocolExposesBoundary oneShot emptyBoundary where
  deliver := fun _ => ()
  exportDemand := fun demand => demand.elim
  accept := fun {demand} _ _ _ => demand.elim
  observe := fun _ => some ()

/-- The projection through it is still order-preserving, as the general theorem says. -/
theorem exposure_projects (trace extension : Trace Unit) :
    emptyExposure.project (trace ++ extension) =
      emptyExposure.project trace ++ emptyExposure.project extension :=
  emptyExposure.project_append trace extension

end Grass.Process.Tests
