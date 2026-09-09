import Grass.Platform.Win32.ProviderResume

namespace Grass.Tests.Win32ProviderResume

open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Memory
open Grass.Platform.Win32 Grass.Platform.Win32.ProviderResume

private def before : State :=
  { machine := .initial .empty
    gpr := fun register => if register = .rsp then 0x1000 else 0xCAFE
    rip := 0x5000
    rflags := 0x10602 }

private def afterRead : MachineState := before.machine
private def resumed := resumedState before 0x1234 afterRead

example : resumed.rip = (0x1234 : BitVec 64) := by decide
example : resumed.gpr .rsp = (0x1008 : BitVec 64) := by decide
example : resumed.gpr .rbx = before.gpr .rbx := by decide
example : resumed.gpr .rax = before.gpr .rax := by decide
example : resumed.rflags = before.rflags := rfl
example : resumed.machine = afterRead := rfl

end Grass.Tests.Win32ProviderResume
