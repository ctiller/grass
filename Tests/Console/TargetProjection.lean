import Grass.Console.CapturedProjection
import Grass.Refinement.Console.WriteWaitingGap
import Grass.Refinement.Console.WriteFileProjection

namespace Grass.Tests.Console.TargetProjection

open Grass.Console Grass.Specification Grass.Semantics Grass.Std.Logical

private def captured : CapturedSpecification ConsoleResourceModel.singleLine Bool :=
  (CapturedSpecification.ofLine _ "é" ⟨true, false, false, false⟩).withLiveness
    .terminatesUnderBoundaryResponse

private def selected := captured.project ⟨TextEncoding.utf8, crlf⟩
  (TargetProjection.successOrFailure true (0 : UInt32) 1)

private def target := selected.target

example : target.payload.length = 4 := by decide
example : target.status .success = 0 := by decide
example : target.status .writeFailed = 1 := by decide
example : target.status .noProgress = 1 := by decide
example : target.status .stdoutUnavailable = 1 := by decide

/-- Inside the multibyte character and inside CRLF remain admissible waits. -/
example : selected.Complete := target.waitingAt ⟨1, by decide⟩
example : selected.Complete := target.waitingAt ⟨3, by decide⟩
example : selected.Complete := target.waitingAt (OutputCut.full _)

/-- Complete output does not imply success: the distinct failure cause survives. -/
example : selected.Complete := target.terminalAt (OutputCut.full _) .writeFailed trivial

/-- The old byte driver cannot cover that full-output permanent wait. -/
example (history : (Grass.Refinement.Console.WriteHistory.system target.payload).History)
    (waiting : Grass.RelationalSystem.PermanentWait
      (Grass.Refinement.Console.WriteWaiting.boundary (fun _ => True)) history) :
    Grass.Refinement.Console.WriteHistory.historyBytes history.path.events ≠ target.payload :=
  Grass.Refinement.Console.WriteWaitingGap.no_full_output_wait (by decide) history waiting

example : CapturedTargetProjection captured UInt32 := selected
example : selected.resourceSemantics = captured.context.resourceSemantics := rfl

/-- Another resource value cannot silently replace the projection's index. -/
example {R : Type} [Grass.Resource.ResourceModel R] {firstResource secondResource : R}
    (first : CapturedSpecification firstResource Bool)
    (_second : CapturedSpecification secondResource Bool)
    (_projection : CapturedTargetProjection first UInt32) : True := by
  fail_if_success
    have _wrong : CapturedTargetProjection _second UInt32 := _projection
  trivial

/-- Even with identical request/resources, a newly appended suite is distinct. -/
example : True := by
  fail_if_success
    have _wrong : CapturedTargetProjection
      (captured.withLiveness .terminatesUnderBoundaryResponse) UInt32 := selected
  trivial

end Grass.Tests.Console.TargetProjection
