import Grass.Console.LineBehavior
import Grass.Console.Accounting

namespace Grass.Tests.Console.LineBehavior

open Grass.Specification Grass.Semantics Grass.Console Grass.RelationalSystem

private def request : LineRequest Bool :=
  ⟨"é", ⟨true, false, false, false⟩⟩

private def rendering : LineRendering := ⟨TextEncoding.utf8, "\r\n"⟩
private def characterInterior : OutputCut (rendering.bytes request.line) := ⟨1, by decide⟩
private def newlineInterior : OutputCut (rendering.bytes request.line) := ⟨3, by decide⟩

example : characterInterior.emitted.toList = [0xC3] := rfl
example : newlineInterior.emitted.toList = [0xC3, 0xA9, 0x0D] := rfl

/-- The actual history at an undecodable UTF-8 cut retains the emitted byte. -/
example : (Behavior.emittedBytes
    (Behavior.pendingAt _ characterInterior).path.events).toList = [0xC3] := by
  rw [Accounting.history_accounting, Behavior.pendingAt_state]
  rfl

/-- Waiting inside CRLF retains the output before the missing LF. -/
example : (Behavior.emittedBytes
    (Behavior.pendingAt _ newlineInterior).path.events).toList = [0xC3, 0xA9, 0x0D] := by
  rw [Accounting.history_accounting, Behavior.pendingAt_state]
  rfl

/-- The request itself supplies actual complete waits inside both encodings. -/
example : request.Complete rendering := request.waitingAt rendering characterInterior
example : request.Complete rendering := request.waitingAt rendering newlineInterior

/-- A failed result can follow emission of the complete logical line. -/
example : request.Complete rendering :=
  request.terminalAt rendering (OutputCut.full _) .writeFailed trivial

/-- Public policy combines failures without identifying diagnostic causes. -/
example : request.outcome .writeFailed = request.outcome .noProgress := rfl
example : Behavior.TerminalCause.writeFailed ≠ .noProgress := by intro h; cases h

end Grass.Tests.Console.LineBehavior
