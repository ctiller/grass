import Grass.Frontend.Target
import Grass.Assembly.StaticObjects

namespace Grass.Tests.Frontend

-- Deliberately no DecidableEq: these authored construction terms must compute.
inductive Outcome where | success | failure

def resources := ConsoleResourceModel.singleLine
def message : Specification.TextLine := "Hello, World!"
def policy : ConsoleWriteOutcomePolicy Outcome := ⟨.success, .failure, .failure, .failure⟩
def spec := SpecProcess.ofRelational (Console.writeLineContract resources message policy)
  |>.withLiveness (.terminatesUnder [.environmentResponsive])

def targetPolicy : TargetOutcomeProjection Outcome UInt32 :=
  .successOrFailure (success := .success) (successCode := 0) (failureCode := 1)
def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ConsoleText (newline := .crlf) (encoding := .utf8)
    (outcome := targetPolicy)
def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64SynchronousStdoutOnly projection
def payload : Std.Logical.ByteArray := projection.encodeLine message
def statics : StaticObjectTable := static_objects {
  rodata align 1 { payload: bytes payload }
}

example : payload.toList = [72,101,108,108,111,44,32,87,111,114,108,100,33,13,10] := by decide
example : projection.captured.view.request.line = message := rfl
example : projection.captured.target.payload = payload := rfl
example : targetPolicy.encode .success = 0 := TargetOutcomeProjection.encode_success ..
example : targetPolicy.encode .failure = 1 :=
  TargetOutcomeProjection.encode_failure _ _ _ _ (by intro impossible; cases impossible)

-- A different actual line produces different statics; it is never substituted
-- with the line captured by the specification during executable construction.
example : projection.encodeLine ("Other" : Specification.TextLine) ≠ payload := by decide
example : (statics.lookup? "payload").map Assembly.StaticObjects.Declaration.bytes = some payload := by
  rfl

end Grass.Tests.Frontend
