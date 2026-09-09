import Grass.Console.CapturedProjection
import Grass.Refinement.Console.WriteWaitingGap
import Grass.Refinement.Console.WriteFileProjection

namespace Grass.Tests.Console.TargetProjection

open Grass.Console Grass.Specification Grass.Semantics Grass.Std.Logical

private def captured : SpecProcess ConsoleResourceModel.singleLine :=
  (SpecProcess.ofRelational (Grass.Console.writeLineContract _ "é" ⟨true, false, false, false⟩)).withLiveness
    (.terminatesUnder [.environmentResponsive])

private def selected := captured.project ⟨TextEncoding.utf8, crlf⟩
  (TargetProjection.successOrFailure (Outcome := Bool) true (0 : UInt32) 1)

private def target := selected.target

example : target.payload.length = 4 := by decide
example : target.status .success = 0 := by decide
example : target.status .writeFailed = 1 := by decide
example : target.status .noProgress = 1 := by decide
example : target.status .stdoutUnavailable = 1 := by decide

/-- Inside the multibyte character and inside CRLF remain admissible waits. -/
example : selected.componentComplete := target.waitingAt ⟨1, by decide⟩
example : selected.componentComplete := target.waitingAt ⟨3, by decide⟩
example : selected.componentComplete := target.waitingAt (OutputCut.full _)

/-- Complete output does not imply success: the distinct failure cause survives. -/
example : selected.componentComplete := target.terminalAt (OutputCut.full _) .writeFailed trivial

/-- The old byte driver cannot cover that full-output permanent wait. -/
example (history : (Grass.Refinement.Console.WriteHistory.system target.payload).History)
    (waiting : Grass.RelationalSystem.PermanentWait
      (Grass.Refinement.Console.WriteWaiting.boundary (fun _ => True)) history) :
    Grass.Refinement.Console.WriteHistory.historyBytes history.path.events ≠ target.payload :=
  Grass.Refinement.Console.WriteWaitingGap.no_full_output_wait (by decide) history waiting

example : CapturedTargetProjection captured UInt32 := selected
example : selected.resourceSemantics = selected.view.snapshot := rfl
example : captured.contract = ofCapturedLine selected.view.request selected.view.snapshot :=
  selected.view.captured
example : selected.wholeModel = ObservedBehavior.model selected.view.request target.rendering :=
  selected.wholeModel_exact

/-- Another resource value cannot silently replace the projection's index. -/
example {R : Type} [Grass.Resource.ResourceModel R] {firstResource secondResource : R}
    (first : SpecProcess firstResource)
    (_second : SpecProcess secondResource)
    (_projection : CapturedTargetProjection first UInt32) : True := by
  fail_if_success
    have _wrong : CapturedTargetProjection _second UInt32 := _projection
  trivial

/-- Even with identical request/resources, a newly appended suite is distinct. -/
example : True := by
  fail_if_success
    have _wrong : CapturedTargetProjection
      (captured.withLiveness (.terminatesUnder [.environmentResponsive])) UInt32 := selected
  trivial

/-- A logical component finish cannot be passed off as observed program completion. -/
example : True := by
  fail_if_success
    have _wrong : selected.wholeModel.Complete :=
      target.terminalAt (OutputCut.full _) .writeFailed trivial
  trivial

end Grass.Tests.Console.TargetProjection
