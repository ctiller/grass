import Grass.Frontend.AssemblySyntax
import Tests.Frontend.Target

namespace Grass.Tests.Frontend

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def otherSpec := SpecProcess.ofRelational
  (Console.writeLineContract resources ("Other" : Specification.TextLine) policy)
def otherProjection : TargetProjection otherSpec .win10X64 :=
  TargetProjection.win10ConsoleText (newline := .crlf) (encoding := .utf8)
    (outcome := targetPolicy)
def otherPlan : PlatformPlan otherSpec.driverBoundary.requirements :=
  PlatformPlan.win10X64SynchronousStdoutOnly otherProjection

example (_value : MachineSource plan) : True := by
  fail_if_success have : MachineSource otherPlan := _value
  trivial

-- Structural assembly construction, independent of any prescribed API sequence.
def arrêt : MachineSource plan :=
  withCallFrame ExitProcess asm_source (statics := statics) {
start:
  mov ecx, 7
  call qword ptr [rip + __imp_ExitProcess]
  ud2
}

def localCode : MachineSource plan :=
  withStack (scratch : UInt32 := 3)
  withStack (spare : UInt32 := 9)
  withCallFrame ExitProcess asm_source (statics := statics) {
begin:
  mov eax, scratch
  mov ecx, spare
  call qword ptr [rip + __imp_ExitProcess]
  ud2
}

example : arrêt.table = statics := rfl
example : arrêt.construction.frame.header.locals = [] := by decide +kernel
example : localCode.construction.frame.header.locals.map (·.name) = ["scratch", "spare"] := by decide +kernel
example : localCode.construction.frame.header.locals.map (·.initialValue.toNat) = [3, 9] := by decide +kernel
example : (Assembly.SourceInput.captureSourceChars arrêt.authored arrêt.offsets).toOption =
    some arrêt.body := arrêt.ingress
example : (MachineSource.ofSource? plan arrêt.authored
    { arrêt.offsets with bodyStart := arrêt.offsets.bodyStart + 1 } statics).isNone := by decide +kernel
example : (MachineSource.ofSource? plan [] arrêt.offsets statics).isNone := by decide +kernel

/-- error: unsupported stack-local type; this construction backend supports UInt32 -/
#guard_msgs in
def unsupportedLocal : MachineSource plan :=
  withStack (wide : UInt64 := 0)
  withCallFrame ExitProcess asm_source (statics := statics) {
  ud2
}

end Grass.Tests.Frontend
