import Grass.Platform.Win32.GetStdHandleRuntime
import Grass.Platform.Win32.WriteFileHandoff
import Tests.Platform.Win32WriteFileStackPlan

/-!
# Shared Win32 protocol-entry regression

Both API adapters below consume the same actual synthetic CALL result and the
same canonical protocol-entry producer.  Passing the WriteFile-target fixture
through the GetStdHandle ABI-plan door tests shared return/home bookkeeping
only; it is not a GetStdHandle dispatch or native-provider claim.
-/

namespace Grass.Tests.Win32ProtocolEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32 Grass.Platform.Win32.ExecutionState
open Grass.Platform.Win32.ProtocolEntry

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def protocol : CallProtocol.State ApiRequest :=
  CallProtocol.initial Grass.Tests.Win32WriteFileStackPlan.called.result.machine
    FreshSupply.initial (by decide)

def before : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol protocol Grass.Tests.Win32WriteFileStackPlan.called.result rfl
    (.caller Grass.Tests.Win32WriteFileStackPlan.inputs.thread)

def commonPlan := Grass.Tests.Win32WriteFileStackPlan.commonResult.toOption.get (by decide)
def writePlan := Grass.Tests.Win32WriteFileStackPlan.writeFileResult.toOption.get (by decide)
def agent := Grass.Tests.Win32WriteFileStackPlan.inputs.independentContext

def getStdHandoff :=
  GetStdHandle.entryHandoff? before commonPlan agent |>.get (by decide)

def writeHandoff :=
  WriteFile.entryHandoff? before Grass.Tests.Win32WriteFileStackPlan.request writePlan agent
    |>.get (by decide)

theorem getStd_entry_succeeds :
    (GetStdHandle.entryHandoff? before commonPlan agent).isSome := by decide

theorem writeFile_entry_succeeds :
    (WriteFile.entryHandoff? before Grass.Tests.Win32WriteFileStackPlan.request
      writePlan agent).isSome := by decide

theorem getStd_complete_batch_length : commonPlan.requests.length = 2 := by decide

theorem writeFile_complete_batch_length :
    (writePlan.loanPlan.requests Grass.Tests.Win32WriteFileStackPlan.request).length = 5 := by
  decide

theorem getStd_request_is_canonical :
    getStdHandoff.pendingRecord.request =
      .getStdHandle (GetStdHandle.selector before.machine) := rfl

theorem writeFile_request_is_canonical :
    writeHandoff.pendingRecord.request =
      .writeFile Grass.Tests.Win32WriteFileStackPlan.request := rfl

/-- The actual minted grant records follow each adapter's complete ordered
loan batch, rather than a separately supplied list. -/
theorem getStd_minted_full_ordered_batch :
    getStdHandoff.pendingRecord.loans =
      (GrantMint.mint getStdHandoff.beforeProtocol.grantSupply
        (commonPlan.requests.map (fun loan =>
          loan.grant getStdHandoff.caller agent))).1 := by
  change (ProtocolEntry.Entry.pendingRecord getStdHandoff).loans = _
  exact (ProtocolEntry.Entry.record_fields getStdHandoff).2.2.2

theorem writeFile_minted_full_ordered_batch :
    writeHandoff.pendingRecord.loans =
      (GrantMint.mint writeHandoff.beforeProtocol.grantSupply
        ((writePlan.loanPlan.requests Grass.Tests.Win32WriteFileStackPlan.request).map
          (fun loan => loan.grant writeHandoff.caller agent))).1 := by
  change (ProtocolEntry.Entry.pendingRecord writeHandoff).loans = _
  exact (ProtocolEntry.Entry.record_fields writeHandoff).2.2.2

theorem getStd_storage_unchanged :
    getStdHandoff.afterProtocol.machine.memory.allocations = before.machine.machine.memory.allocations ∧
    getStdHandoff.afterProtocol.machine.memory.backings = before.machine.machine.memory.backings :=
  getStdHandoff.storage_unchanged

theorem writeFile_storage_unchanged :
    writeHandoff.afterProtocol.machine.memory.allocations = before.machine.machine.memory.allocations ∧
    writeHandoff.afterProtocol.machine.memory.backings = before.machine.machine.memory.backings :=
  writeHandoff.storage_unchanged

theorem getStd_fresh_and_recorded :
    getStdHandoff.beforeProtocol.pending.lookup getStdHandoff.call = none ∧
    getStdHandoff.afterProtocol.pending.lookup getStdHandoff.call =
      some getStdHandoff.pendingRecord :=
  ⟨getStdHandoff.fresh, getStdHandoff.recorded⟩

theorem writeFile_fresh_and_recorded :
    writeHandoff.beforeProtocol.pending.lookup writeHandoff.call = none ∧
    writeHandoff.afterProtocol.pending.lookup writeHandoff.call =
      some (WriteFile.embedPending writeHandoff.record) :=
  ⟨ProtocolEntry.Entry.fresh writeHandoff, writeHandoff.recorded⟩

def unrelatedCall := getStdHandoff.afterProtocol.callSupply.fresh.1

theorem unrelated_call_is_distinct : unrelatedCall ≠ getStdHandoff.call := by decide

theorem shared_entry_frames_other_pending_key :
    getStdHandoff.afterProtocol.pending.lookup unrelatedCall =
      getStdHandoff.beforeProtocol.pending.lookup unrelatedCall :=
  ProtocolEntry.Entry.other_pending getStdHandoff unrelated_call_is_distinct

def pendingControl : ExecutionState.State ApiRequest :=
  { before with control := (ExecutionState.Control.pending writeHandoff.call
      Grass.Tests.Win32WriteFileStackPlan.inputs.thread agent) }

theorem pending_control_refuses_getStd :
    GetStdHandle.entryHandoff? pendingControl commonPlan agent = none := by decide

theorem caller_context_refuses_as_provider :
    WriteFile.entryHandoff? before Grass.Tests.Win32WriteFileStackPlan.request writePlan
      Grass.Tests.Win32WriteFileStackPlan.inputs.thread = none := by decide

end Grass.Tests.Win32ProtocolEntry
