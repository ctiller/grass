import Grass.Console.LineBehavior
import Grass.Console.Accounting

/-! Representation and public-status selection for the exact authored request.
This is projection data, not a replacement certificate gate or a provider proof.
The component complete history carrier is unchanged, so selection cannot discard a choice,
an unfavorable result, or a permitted permanent wait. Actual OS status observation
must still be connected to `status` by the provider/terminal bridge.
-/

namespace Grass.Console

open Specification Semantics RelationalSystem Std.Logical

structure TargetProjection {Outcome : Type} (request : LineRequest Outcome) (Status : Type) where
  rendering : LineRendering
  encodeOutcome : Outcome → Status

namespace TargetProjection

variable {Outcome Status : Type} {request : LineRequest Outcome}

def payload (projection : TargetProjection request Status) : Vec Byte :=
  projection.rendering.bytes request.line

def componentSystem (projection : TargetProjection request Status) : RelationalSystem Behavior.Event :=
  request.system projection.rendering

abbrev componentComplete (projection : TargetProjection request Status) :=
  request.Complete projection.rendering

def status (projection : TargetProjection request Status) (cause : Behavior.TerminalCause) : Status :=
  projection.encodeOutcome (request.outcome cause)

/-- Target representation does not introduce an independently chosen behavior. -/
theorem componentSystem_exact (projection : TargetProjection request Status) :
    projection.componentSystem = Behavior.system projection.payload := rfl

/-- This identity retains the original choices and intermediate frontiers too. -/
theorem componentComplete_exact (projection : TargetProjection request Status) :
    projection.componentComplete = request.Complete projection.rendering := rfl

/-- Finite emitted bytes equal the cut in this history's exact finished state. -/
theorem terminal_accounting (projection : TargetProjection request Status)
    (history : projection.componentSystem.History) (cut : OutputCut projection.payload)
    (cause : Behavior.TerminalCause) (atCut : history.state = .finished cut cause) :
    Behavior.emittedBytes history.path.events = cut.emitted := by
  have accounting := Accounting.history_accounting (payload := projection.payload) history
  exact accounting.trans (congrArg Accounting.committed atCut)

/-- Every byte cut remains a complete permanent-wait behavior after projection. -/
def waitingAt (projection : TargetProjection request Status) (cut : OutputCut projection.payload) :
    projection.componentComplete := request.waitingAt projection.rendering cut

/-- No status selection removes any allowed terminal cause at any cut. -/
def terminalAt (projection : TargetProjection request Status) (cut : OutputCut projection.payload)
    (cause : Behavior.TerminalCause) (allowed : Behavior.FinishAllowed cut cause) :
    projection.componentComplete := request.terminalAt projection.rendering cut cause allowed

/-- The representation selected by authored Windows Hello; no message or policy
is copied here. Other targets can select another lawful rendering. -/
def utf8CRLF (request : LineRequest Outcome) (encodeOutcome : Outcome → Status) :
    TargetProjection request Status :=
  ⟨⟨TextEncoding.utf8, crlf⟩, encodeOutcome⟩

theorem utf8CRLF_payload (encodeOutcome : Outcome → Status) :
    (utf8CRLF request encodeOutcome).payload = Text.utf8 (request.line.text ++ crlf) := rfl

/-- Success/failure coding tests the authored public outcome, not the diagnostic
cause. Whether those outcomes are distinct remains the authored policy's fact. -/
def successOrFailure [DecidableEq Outcome] (success : Outcome) (successCode failureCode : Status) :
    Outcome → Status := fun result => if result = success then successCode else failureCode

theorem success_status (projection : TargetProjection request Status) :
    projection.status .success = projection.encodeOutcome request.policy.success := rfl

theorem writeFailed_status (projection : TargetProjection request Status) :
    projection.status .writeFailed = projection.encodeOutcome request.policy.writeFailed := rfl

theorem noProgress_status (projection : TargetProjection request Status) :
    projection.status .noProgress = projection.encodeOutcome request.policy.noProgress := rfl

theorem unavailable_status (projection : TargetProjection request Status) :
    projection.status .stdoutUnavailable = projection.encodeOutcome request.policy.stdoutUnavailable := rfl

end TargetProjection
end Grass.Console
