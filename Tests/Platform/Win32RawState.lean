import Grass.Platform.Win32.RawState
import Tests.Platform.Win32ApiRequest

namespace Grass.Tests.Win32RawState

open Grass.Platform.Win32 Grass.Platform.Win32.ExecutionState
open Grass.Tests.Win32ApiRequest

private def cpu : Grass.ISA.X86.Execution.State :=
  { machine := afterWrite.machine, gpr := fun _ => 0, rip := 0, rflags := 0 }

private def checked : State ApiRequest :=
  State.ofCallProtocol afterWrite cpu rfl
    (.pending writeCall Grass.Tests.Spike1.mainThread Grass.Tests.Spike1.apiAgent)

example : checked.raw.checked? = some checked := checked.raw_checked?

/-- The original pending loans no longer match after the real full return.
The raw state still carries that reached machine and the original metadata. -/
private def mismatched : RawState :=
  checked.raw.withMachine { cpu with machine := afterReturn.machine }

example : mismatched.checked? = none := by decide

example : mismatched.machine.machine = afterReturn.machine := rfl

example : mismatched.metadata = checked.metadata := rfl

example : mismatched.control = checked.control := rfl

/-- The unrelated pending call is retained in the original metadata even when
the checked projection refuses this particular machine/metadata pairing. -/
example : mismatched.metadata.pending.lookup stdCall = some stdRecord := rfl

example : ¬ mismatched.ProtocolValid :=
  (mismatched.checked?_eq_none).mp (by decide)

end Grass.Tests.Win32RawState
