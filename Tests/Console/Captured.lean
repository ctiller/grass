import Grass.Console.Captured
import Grass.Semantics.SpecProcess

namespace Grass.Tests.Console.Captured

open Grass.Console Grass.Specification Grass.Semantics

private def base : CapturedSpecification ConsoleResourceModel.singleLine Bool :=
  CapturedSpecification.ofLine _ "é" ⟨true, false, false, false⟩

private def once := base.withLiveness .terminatesUnderBoundaryResponse
private def twice := once.withLiveness .terminatesUnderBoundaryResponse

example : twice.suite.liveness =
    [.terminatesUnderBoundaryResponse, .terminatesUnderBoundaryResponse] := rfl
example : twice.context.request.line.text = "é" := rfl
example : twice.context.request.policy.writeFailed = false := rfl
example : twice.context.resourceSemantics = base.context.resourceSemantics := rfl

private def rendering : LineRendering := ⟨TextEncoding.utf8, "\r\n"⟩

/-- Appending liveness does not delete permanent waiting after complete output. -/
example : twice.Complete rendering :=
  base.context.request.waitingAt rendering (OutputCut.full _)

/- No implicit acceptance route from the staging type to the existing root. -/
/--
error: Type mismatch
  base
has type
  CapturedSpecification ConsoleResourceModel.singleLine Bool
of sort `Type` but is expected to have type
  SpecProcess ConsoleResourceModel.singleLine
of sort `Type 2`
-/
#guard_msgs in
#check (base : Grass.SpecProcess ConsoleResourceModel.singleLine)

end Grass.Tests.Console.Captured
