import Grass.ISA.X86.Execution.Fetch
import Grass.ISA.X86.Execution.StackInstruction
import Grass.ISA.X86.Execution.CompletionFlags
import Grass.Op.WriteCompletion

/-!
# The bounded normal register PUSH completion branch

A receipt connects the actual instruction fetch to an actual eight-byte store.
The payload is the pre-instruction register value, including when the source is
RSP. The bounded stack profile excludes subtraction wrap. This normal branch
does not exclude faults, traps or interruptions from other executions.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

/-- Inputs joining an actual fetched register PUSH to its actual prepared store. -/
structure PushNormal (before : State) (afterFetch afterStore : MachineState)
    (register : Gpr) where
  fetch : FetchedSite before afterFetch
  encoding : fetch.site.encoding = (StackInstruction.push register).encoding
  descriptor : AccessDescriptor
  store : AccessRun afterFetch afterStore descriptor
  /-- The store changes the instruction payload oracle within the same policy. -/
  policy : store.policy = { fetch.run.policy with oracle := store.policy.oracle }
  context : store.context = fetch.run.context
  contextKind : store.contextKind = fetch.run.contextKind
  cause : store.cause = fetch.run.cause
  fetchContext : fetch.descriptor.context = fetch.run.context
  storeContext : descriptor.context = store.context
  memoryOracle : store.policy.oracle =
    Oracle.ofMemory (fun _ _ => le64 (before.gpr register)) (fun _ _ _ => 0)
  intent : descriptor.intent = .write
  initialization : descriptor.initialization = .readsNothing
  ordering : descriptor.ordering = .plain
  extent : descriptor.range.size = 8
  initialized : descriptor.producesInitialized = true
  ledgerEffect : descriptor.ledgerEffect = []
  authorityEffect : descriptor.authorityEffect = []
  /-- The bounded normal stack profile admits the eight-byte decrement. -/
  stackNoUnderflow : 8 ≤ (before.gpr .rsp).toNat
  address : descriptor.address = .numeric (before.gpr .rsp - 8)
  placed : ∃ base, store.resolved.allocation.base = some base

namespace PushNormal

/-- `written_exact` derives the stored pre-instruction value from the actual oracle answer. -/
theorem written_exact {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    receipt.store.complete.committed.written = some (le64 (before.gpr register)) := by
  have answer : (Oracle.ofMemory (fun _ _ => le64 (before.gpr register))
      (fun _ _ _ => 0)).answerResolved
      (afterFetch.noteContext receipt.store.context receipt.store.contextKind)
      receipt.descriptor receipt.store.resolved = some receipt.store.complete := by
    rw [← receipt.memoryOracle]
    exact receipt.store.answerResolved
  have written := Oracle.ofMemory_written_of_answerResolved
    (fun _ _ => le64 (before.gpr register)) (fun _ _ _ => 0)
    (afterFetch.noteContext receipt.store.context receipt.store.contextKind)
    receipt.descriptor receipt.store.resolved receipt.store.complete answer
    (by rw [receipt.intent]; rfl)
  simpa [receipt.extent, le64] using written

/-- `memory_written` derives the initialized backing mutation from the actual checked store. -/
theorem memory_written {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    afterStore.memory =
      (afterFetch.noteContext receipt.store.context receipt.store.contextKind).memory.writeResolved
        receipt.store.resolved (le64 (before.gpr register)) true
        (receipt.store.complete.committed.writtenFits _ receipt.written_exact) := by
  obtain ⟨space, found, wellFormed⟩ := receipt.store.wellFormed
  have written := clean_prepared_complete_memory_eq_commitResolved receipt.store.policy
    (afterFetch.noteContext receipt.store.context receipt.store.contextKind) afterStore
    receipt.descriptor receipt.store.resolved receipt.store.prepared receipt.store.complete
    receipt.store.contextKind receipt.store.cause space found wellFormed
    receipt.store.prepared_result receipt.store.clean receipt.ledgerEffect receipt.authorityEffect
  have committed := Grass.Memory.commitResolved_of_eq_some
    (afterFetch.noteContext receipt.store.context receipt.store.contextKind).memory
    receipt.descriptor receipt.store.resolved receipt.store.complete.committed.written
    receipt.store.complete.committed.writtenFits (le64 (before.gpr register)) receipt.written_exact
  exact written.trans (by simpa only [receipt.initialized] using committed)

/-- `saved_cell` observes every byte and initialization bit in the actual saved stack span. -/
theorem saved_cell {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) (offset : Nat)
    (covered : receipt.descriptor.range.Covers offset) :
    afterStore.memory.cellAt? receipt.descriptor.provenance.root offset =
      ((le64 (before.gpr register))[offset - receipt.descriptor.range.start]?).map (·, true) := by
  rw [receipt.memory_written]
  apply MemoryState.cellAt?_writeResolved_of_covers
  simpa [le64, ← receipt.extent] using covered

/-- The architectural result contains the actual store's memory machine. -/
def result {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) : State :=
  { before.withGpr .rsp (before.gpr .rsp - 8) with
    machine := afterStore
    rip := receipt.fetch.site.fallthroughRip
    rflags := completedPushRflags before }

/-- `rsp_exact` derives the decremented stack pointer from the pre-instruction state. -/
theorem rsp_exact {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    receipt.result.gpr .rsp = before.gpr .rsp - 8 := by
  simp [result, State.withGpr]

/-- `rsp_toNat` uses the receipt's stack bound to exclude modular subtraction wrap. -/
theorem rsp_toNat {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    (receipt.result.gpr .rsp).toNat = (before.gpr .rsp).toNat - 8 := by
  rw [receipt.rsp_exact]
  have bound : (8 : BitVec 64) ≤ before.gpr .rsp := by
    change 8 ≤ (before.gpr .rsp).toNat
    exact receipt.stackNoUnderflow
  exact BitVec.toNat_sub_of_le bound

/-- `gpr_frame` retains each register other than RSP. -/
theorem gpr_frame {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) (otherRegister : Gpr)
    (other : otherRegister ≠ .rsp) :
    receipt.result.gpr otherRegister = before.gpr otherRegister := by
  simp [result, State.withGpr, other]

/-- The next RIP is the fallthrough of the whole fetched instruction. -/
theorem rip_exact {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    receipt.result.rip = receipt.fetch.site.fallthroughRip := rfl

/-- The ordinary completion RFLAGS transfer includes RF clearing. -/
theorem rflags_exact {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    receipt.result.rflags = completedPushRflags before := rfl

/-- Successful preparation locates the store in its present placed allocation. -/
theorem placement {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    ∃ base, receipt.store.resolved.allocation.base = some base ∧
      FitsAllocation base receipt.store.resolved.allocation.extent.stop ∧
      addressOf base receipt.descriptor.range.start = before.gpr .rsp - 8 := by
  obtain ⟨base, placed⟩ := receipt.placed
  obtain ⟨fits, address⟩ := prepared_base_fits_and_address receipt.store.prepared placed
  exact ⟨base, placed, fits, Address.numeric.inj (address.symm.trans receipt.address)⟩

/-- `fetched_event` connects the selected register to the actual instruction bytes. -/
theorem fetched_event {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    ∃ valid, afterFetch.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some (StackInstruction.push register).encoding.toBytes := by
  obtain ⟨valid, appended, bytes, _⟩ := receipt.fetch.completed_event
  exact ⟨valid, appended, by simpa [receipt.encoding] using bytes⟩

/-- `stored_event` records the exact eight-byte payload in the actual completed store event. -/
theorem stored_event {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    ∃ valid, afterStore.events = afterFetch.events ++ [valid] ∧
      valid.event.valueWritten = some (le64 (before.gpr register)) ∧
      valid.event.status = .completed 0 8 := by
  obtain ⟨space, valid, _, event, appended, _, _, _⟩ := receipt.store.completed_event
  have fields := completedEvent_fields event
  have reads : receipt.descriptor.intent.reads = false := by rw [receipt.intent]; rfl
  have writes : receipt.descriptor.intent.writes = true := by rw [receipt.intent]; rfl
  have count := receipt.store.complete.writesFull writes
  have zero : receipt.store.complete.committed.readCount = 0 := by
    simp [Committed.readCount, receipt.store.complete.committed.observedAbsent reads]
  refine ⟨valid, appended, fields.2.2.2.2.2.2.2.2.trans receipt.written_exact, ?_⟩
  simpa [count, zero, receipt.extent] using fields.2.2.2.2.2.2.1

/-- `events_exact` orders the typed fetch and saved-value store in the same actual trace. -/
theorem events_exact {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    ∃ fetched stored, receipt.result.machine.events = before.machine.events ++ [fetched, stored] ∧
      fetched.event.valueRead = some (StackInstruction.push register).encoding.toBytes ∧
      stored.event.valueWritten = some (le64 (before.gpr register)) := by
  obtain ⟨fetched, fetchAppended, fetchedBytes⟩ := receipt.fetched_event
  obtain ⟨stored, storeAppended, storedBytes, _⟩ := receipt.stored_event
  refine ⟨fetched, stored, ?_, fetchedBytes, storedBytes⟩
  change afterStore.events = _
  rw [storeAppended, fetchAppended, List.append_assoc]
  rfl

/-- `obligations_frame` composes the neutral actual fetch and store ledger frames. -/
theorem obligations_frame {before : State} {afterFetch afterStore : MachineState} {register : Gpr}
    (receipt : PushNormal before afterFetch afterStore register) :
    receipt.result.machine.obligations = before.machine.obligations := by
  change afterStore.obligations = _
  rw [receipt.store.prepared_result]
  exact (performPreparedAccess_noLedgerEffect_obligations receipt.store.policy
    (afterFetch.noteContext receipt.store.context receipt.store.contextKind) receipt.descriptor
    receipt.store.resolved receipt.store.prepared (.completed receipt.store.complete)
    receipt.store.contextKind receipt.store.cause receipt.ledgerEffect).trans receipt.fetch.state_frame.2

end PushNormal
end Grass.ISA.X86.Execution
