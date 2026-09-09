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

/-- Runtime data is retained explicitly through the checked view. A protocol
check alone intentionally does not establish endpoint-runtime validity. -/
private def withRuntime := checked.raw
  ((Grass.Std.Logical.FiniteMap.empty.insert stdCall CallRuntime.exitProcess).insert
    writeCall CallRuntime.exitProcess)

example : withRuntime.checked? = some checked := checked.raw_checked? _

example : checked.raw withRuntime.calls = withRuntime :=
  RawState.checked?_raw (raw := withRuntime) (by exact checked.raw_checked? _)

example : (withRuntime.eraseCall writeCall).calls.lookup stdCall = some .exitProcess := by
  rw [RawState.eraseCall_other withRuntime mixed_pending_entries_retained_and_calls_distinct.2.2]
  rfl

example : (withRuntime.eraseCall writeCall).calls.lookup writeCall = none :=
  withRuntime.eraseCall_lookup writeCall

/-- An ExitProcess runtime tag cannot stand in for a pending GetStdHandle,
even though the unchanged protocol metadata itself still checks. -/
example : ¬ withRuntime.RuntimeLinked := by
  intro linked
  have present : (stdCall, CallRuntime.exitProcess) ∈ withRuntime.calls.entries :=
    Grass.Std.Logical.FiniteMap.mem_of_lookup
      (show withRuntime.calls.lookup stdCall = some CallRuntime.exitProcess from rfl)
  obtain ⟨pending, lookup, kind⟩ := linked.1 _ present
  have expected : withRuntime.metadata.pending.lookup stdCall = some stdRecord := rfl
  have same := Option.some.inj (lookup.symm.trans expected)
  subst pending
  change False at kind
  exact kind

end Grass.Tests.Win32RawState
