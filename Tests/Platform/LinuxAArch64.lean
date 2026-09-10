import Grass.Platform.Linux.AArch64
import Grass.ISA.AArch64.Source

namespace Tests.Platform.LinuxAArch64
open Grass.ISA.AArch64 Grass.Std.Logical
open Grass.Platform.Linux

def cpu (number : BitVec 64) : Cpu where
  gpr := fun reg =>
    if reg.val = 8 then number
    else if reg.val = 0 then 1
    else if reg.val = 1 then 0x2000
    else if reg.val = 2 then 19
    else 0
  pc := 0x1000
  nzcv := 0

/-- Exercise the actual shared source parser before Linux interpretation. -/
def inspect (bytes : Grass.Std.Logical.ByteArray) (before : Cpu) :
    Option Syscall.Request :=
  match readSource bytes with
  | .done source _ => do
    let instruction ← SupervisorCall.request? source.word before
    (Syscall.AArch64.decode? instruction).map (·.request)
  | _ => none

example : inspect (emitWord (SupervisorCall.encode 0)) (cpu 64) =
    some (.write 1 0x2000 19) := by decide

example : inspect (emitWord (SupervisorCall.encode 0) ++ Vec.fromList [0xaa])
    (cpu 63) = some (.read 1 0x2000 19) := by decide

example : inspect (emitWord (SupervisorCall.encode 0)) (cpu (2^32 + 64)) =
    some (.write 1 0x2000 19) := by decide

example : inspect (emitWord (SupervisorCall.encode 1)) (cpu 64) = none := by decide
example : inspect (emitWord (SupervisorCall.encode 0)) (cpu 999) = none := by decide
example : inspect (emitWord 0) (cpu 64) = none := by decide
example : inspect ((emitWord (SupervisorCall.encode 0)).take 3) (cpu 64) = none := by decide

/-- An existing body receipt is consumed directly, without another ISA decoder. -/
example : (Syscall.AArch64.decode?
    (SupervisorCall.sourceStep 0 (cpu 64)).step.supervisorRequest).map (·.request) =
      some (.write 1 0x2000 19) := by decide

example : (Syscall.AArch64.decode?
    (SupervisorCall.sourceStep 1 (cpu 64)).step.supervisorRequest).isNone = true := by decide

end Tests.Platform.LinuxAArch64
