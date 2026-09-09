import Grass.Platform.Win32.ExitProcessRuntime
import Tests.Platform.Win32ApiRequest

namespace Grass.Tests.Win32ExitProcessRuntime

open Grass.Platform.Win32 Grass.Platform.Win32.ExecutionState
open Grass.Tests.Win32ApiRequest Grass.Tests.Spike1

private def cpu : Grass.ISA.X86.Execution.State :=
  { machine := afterStd.machine.noteContext apiAgent .externalAgent
    gpr := fun register => if register = .rcx then 0x1234567800000001 else 0
    rip := 0, rflags := 0 }

private def before : State ApiRequest :=
  { machine := cpu, metadata := afterStd.metadata, control := .caller mainThread
    protocolValid := by decide }

private def attempt := ExitProcess.entryHandoff? before apiAgent

private theorem accepted : attempt.isSome := by decide

private def handoff := attempt.get accepted

-- High RCX bits do not become part of the DWORD request.
example : ExitProcess.status before.machine = 1 := by decide

example : handoff.afterProtocol.pending.lookup handoff.call =
    some ⟨mainThread, apiAgent, .exitProcess 1, []⟩ := rfl

-- Issuing this occurrence retains an unrelated pending API call.
example : handoff.afterProtocol.pending.lookup stdCall =
    afterStd.pending.lookup stdCall := rfl

-- The caller is suspended; an initializer cannot certify termination.
example : (handoff.initRaw .empty).control = .pending handoff.call mainThread apiAgent := by
  decide

example : (handoff.initRaw .empty).calls.lookup handoff.call = some .exitProcess :=
  handoff.runtime_exact _

-- Re-entering while this caller has a pending occurrence is rejected.
example : (ExitProcess.entryHandoff? handoff.after apiAgent).isNone := by decide

end Grass.Tests.Win32ExitProcessRuntime
