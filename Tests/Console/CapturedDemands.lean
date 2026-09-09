import Grass.Console.CapturedDemands

namespace Grass.Tests.Console.CapturedDemands

open Grass.Console

private def base : CapturedSpecification ConsoleResourceModel.singleLine Bool :=
  CapturedSpecification.ofLine _ "Hello, World!" ⟨true, false, false, false⟩

private def once := base.withLiveness .terminatesUnderBoundaryResponse
private def twice := once.withLiveness .terminatesUnderBoundaryResponse

example : base.demands.keys.length = 3 := rfl
example : once.demands.keys.length = 4 := rfl
example : twice.demands.keys.length = 5 := rfl

/-- Each append retains a separate key even when the liveness text repeats. -/
example : twice.demands.identity ⟨3, by decide⟩ ≠ twice.demands.identity ⟨4, by decide⟩ := by
  intro equal
  have := twice.demands.identityInjective equal
  cases this

example : twice.dependencies ⟨2, by decide⟩ = [.resourceSelection] := rfl
example : twice.demands.kind ⟨4, by decide⟩ = .termination := rfl

/-- The exact computed family has a universal author-side certificate. -/
example : DemandCertificateFamily twice.demands := twice.meetsDemands

/-- The output key denotes exactly the captured output law. -/
example : twice.demands.statement ⟨0, by decide⟩ = twice.context.OutputExact := rfl

end Grass.Tests.Console.CapturedDemands
