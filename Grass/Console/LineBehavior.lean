import Grass.Specification.TextLine
import Grass.Console.Behavior

/-!
# A logical line and its representation-parametric behavior

The component stores the authored text and total public outcome policy, not a
rendering or a retry implementation. `LineRequest.system` and `Complete` expose
the same console semantics for each explicitly supplied lawful rendering.
Resource snapshots, suite capture and the authored liveness theorem are not
implemented here; this is not yet `SpecProcess` or a lowering certificate.
-/

namespace Grass

/-- The authored total policy for the four console terminal causes. -/
structure ConsoleWriteOutcomePolicy (Outcome : Type) where
  success : Outcome
  stdoutUnavailable : Outcome
  writeFailed : Outcome
  noProgress : Outcome

namespace ConsoleWriteOutcomePolicy

/-- Project public outcomes without changing the diagnostic cause in the trace. -/
def apply {Outcome : Type} (policy : ConsoleWriteOutcomePolicy Outcome) :
    Console.Behavior.TerminalCause → Outcome
  | .success => policy.success
  | .stdoutUnavailable => policy.stdoutUnavailable
  | .writeFailed => policy.writeFailed
  | .noProgress => policy.noProgress

end ConsoleWriteOutcomePolicy

namespace Console

open Specification Semantics RelationalSystem
open Std.Logical

/-- One logical request; target encoding and line ending remain parameters of
its denotation rather than fields in the authored component. -/
structure LineRequest (Outcome : Type) where
  line : TextLine
  policy : ConsoleWriteOutcomePolicy Outcome

namespace LineRequest

variable {Outcome : Type}

/-- Instantiate only the representation of the fixed logical request. -/
def system (request : LineRequest Outcome) (rendering : LineRendering) :
    RelationalSystem Behavior.Event := Behavior.system (rendering.bytes request.line)

/-- Complete behaviors retain terminal, infinite and permanent-wait constructors;
their concrete occurrence/frontier and cut data are not projected away. -/
abbrev Complete (request : LineRequest Outcome) (rendering : LineRendering) :=
  CompleteHistory (Behavior.boundary (rendering.bytes request.line))

/-- Every represented byte cut is a reachable permanent-wait behavior, including
cuts within a character or newline. `Behavior.permanentWaitAt` supplies the law. -/
def waitingAt (request : LineRequest Outcome) (rendering : LineRendering)
    (cut : OutputCut (rendering.bytes request.line)) : request.Complete rendering :=
  .waiting (Behavior.pendingAt _ cut) (Behavior.permanentWaitAt _ cut)

/-- Finish the same request at an allowed cut; the terminal event retains its
diagnostic cause independently of the public outcome policy. -/
def terminalAt (request : LineRequest Outcome) (rendering : LineRendering)
    (cut : OutputCut (rendering.bytes request.line)) (cause : Behavior.TerminalCause)
    (allowed : Behavior.FinishAllowed cut cause) : request.Complete rendering :=
  let history := Behavior.pendingAt (rendering.bytes request.line) cut
  let finished := history.append (.snoc .nil (Behavior.Choice.reply cut (.finish cause))
    (.terminal cause) (Behavior.State.finished cut cause) ()
    (by exact ⟨Behavior.pendingAt_state _ cut, allowed, rfl, rfl⟩))
  .terminal finished ⟨cut, cause, rfl, allowed⟩

/-- The same actual diagnostic cause selects the authored public outcome. -/
def outcome (request : LineRequest Outcome) (cause : Behavior.TerminalCause) : Outcome :=
  request.policy.apply cause

/-- No independent payload can replace the rendering derived from the request. -/
theorem system_exact (request : LineRequest Outcome) (rendering : LineRendering) :
    request.system rendering = Behavior.system (rendering.bytes request.line) := rfl

/-- `LineRendering.utf8_bytes_exact` connects this family to canonical UTF-8;
the chosen newline remains explicit, and is never inferred from the platform. -/
theorem utf8_system_exact (request : LineRequest Outcome) (newline : String) :
    request.system { encoding := TextEncoding.utf8, newline := newline } =
      Behavior.system (Text.utf8 (request.line.text ++ newline)) := rfl

/-- Changing the public policy does not change allowed diagnostic histories. -/
theorem policy_preserves_system (line : TextLine)
    (first second : ConsoleWriteOutcomePolicy Outcome) (rendering : LineRendering) :
    (LineRequest.mk line first).system rendering =
      (LineRequest.mk line second).system rendering := rfl

end LineRequest
end Console
end Grass
