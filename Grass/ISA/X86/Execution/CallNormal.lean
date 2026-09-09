import Grass.ISA.X86.Execution.Fetch
import Grass.ISA.X86.Execution.ReadValue64
import Grass.ISA.X86.Execution.CompletionFlags
import Grass.Op.WriteCompletion

/-!
# Conditional normal indirect CALL completion

`CallNormal` connects an actual instruction fetch, initialized target read, and
return-address store. It carries no provider identity or return protocol. These
normal receipts leave canonicality, fault priority and delivery correspondence
to the admitted architectural and platform profile.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

/-- Source-free bounded normal RIP-relative indirect CALL. -/
structure CallNormal (before : State)
    (afterFetch afterRead afterStore : MachineState) (displacement : BitVec 32) where
  fetch : FetchedSite before afterFetch
  encoding : callMem64 (.ripRelative displacement) = some fetch.site.encoding
  readDescriptor : AccessDescriptor
  readRun : AccessRun afterFetch afterRead readDescriptor
  read : ReadValue64 readRun
  readPolicy : readRun.policy = { fetch.run.policy with oracle := readRun.policy.oracle }
  readContext : readRun.context = fetch.run.context
  readContextKind : readRun.contextKind = fetch.run.contextKind
  readCause : readRun.cause = fetch.run.cause
  fetchContext : fetch.descriptor.context = fetch.run.context
  fetchSpace : fetch.descriptor.space = .cpuVirtual
  readDescriptorContext : readDescriptor.context = readRun.context
  readIntent : readDescriptor.intent = .read
  readSpace : readDescriptor.space = .cpuVirtual
  readOrdering : readDescriptor.ordering = .plain
  readLedgerEffect : readDescriptor.ledgerEffect = []
  readAuthorityEffect : readDescriptor.authorityEffect = []
  readAddress : readDescriptor.address = .numeric
    (fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt)
  readPlaced : ∃ base, readRun.resolved.allocation.base = some base
  storeDescriptor : AccessDescriptor
  storeRun : AccessRun afterRead afterStore storeDescriptor
  storePolicy : storeRun.policy = { readRun.policy with oracle := storeRun.policy.oracle }
  storeContext : storeRun.context = readRun.context
  storeContextKind : storeRun.contextKind = readRun.contextKind
  storeCause : storeRun.cause = readRun.cause
  storeDescriptorContext : storeDescriptor.context = storeRun.context
  storeOracle : storeRun.policy.oracle =
    Oracle.ofMemory (fun _ _ => le64 fetch.site.fallthroughRip) (fun _ _ _ => 0)
  storeIntent : storeDescriptor.intent = .write
  storeSpace : storeDescriptor.space = .cpuVirtual
  storeInitialization : storeDescriptor.initialization = .readsNothing
  storeOrdering : storeDescriptor.ordering = .plain
  storeWidth : storeDescriptor.range.size = 8
  storeInitialized : storeDescriptor.producesInitialized = true
  storeLedgerEffect : storeDescriptor.ledgerEffect = []
  storeAuthorityEffect : storeDescriptor.authorityEffect = []
  stackNoUnderflow : 8 ≤ (before.gpr .rsp).toNat
  storeAddress : storeDescriptor.address = .numeric (before.gpr .rsp - 8)
  storePlaced : ∃ base, storeRun.resolved.allocation.base = some base

namespace CallNormal

def result {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) : State :=
  { before.withGpr .rsp (before.gpr .rsp - 8) with
    machine := afterStore
    rip := receipt.read.value
    rflags := completedPushRflags before }

theorem written_exact {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    receipt.storeRun.complete.committed.written =
      some (le64 receipt.fetch.site.fallthroughRip) := by
  have answer : (Oracle.ofMemory (fun _ _ => le64 receipt.fetch.site.fallthroughRip)
      (fun _ _ _ => 0)).answerResolved
      (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind)
      receipt.storeDescriptor receipt.storeRun.resolved = some receipt.storeRun.complete := by
    rw [← receipt.storeOracle]
    exact receipt.storeRun.answerResolved
  have written := Oracle.ofMemory_written_of_answerResolved
    (fun _ _ => le64 receipt.fetch.site.fallthroughRip) (fun _ _ _ => 0)
    (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind)
    receipt.storeDescriptor receipt.storeRun.resolved receipt.storeRun.complete answer
    (by rw [receipt.storeIntent]; rfl)
  simpa [receipt.storeWidth, le64] using written

theorem memory_written {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    afterStore.memory =
      (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind).memory.writeResolved
        receipt.storeRun.resolved (le64 receipt.fetch.site.fallthroughRip) true
        (receipt.storeRun.complete.committed.writtenFits _ receipt.written_exact) := by
  obtain ⟨space, found, wellFormed⟩ := receipt.storeRun.wellFormed
  have written := clean_prepared_complete_memory_eq_commitResolved receipt.storeRun.policy
    (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind) afterStore
    receipt.storeDescriptor receipt.storeRun.resolved receipt.storeRun.prepared
    receipt.storeRun.complete receipt.storeRun.contextKind receipt.storeRun.cause space found
    wellFormed receipt.storeRun.prepared_result receipt.storeRun.clean
    receipt.storeLedgerEffect receipt.storeAuthorityEffect
  have committed := Grass.Memory.commitResolved_of_eq_some
    (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind).memory
    receipt.storeDescriptor receipt.storeRun.resolved receipt.storeRun.complete.committed.written
    receipt.storeRun.complete.committed.writtenFits
    (le64 receipt.fetch.site.fallthroughRip) receipt.written_exact
  exact written.trans (by simpa only [receipt.storeInitialized] using committed)

theorem saved_cell {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) (offset : Nat)
    (covered : receipt.storeDescriptor.range.Covers offset) :
    afterStore.memory.cellAt? receipt.storeDescriptor.provenance.root offset =
      ((le64 receipt.fetch.site.fallthroughRip)[offset -
        receipt.storeDescriptor.range.start]?).map (·, true) := by
  rw [receipt.memory_written]
  apply MemoryState.cellAt?_writeResolved_of_covers
  simpa [le64, ← receipt.storeWidth] using covered

theorem read_state_frame {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    afterRead.memory = afterFetch.memory ∧ afterRead.obligations = afterFetch.obligations := by
  rw [receipt.readRun.prepared_result]
  exact performPreparedAccess_readOnly_noEffects_frame receipt.readRun.policy
    (afterFetch.noteContext receipt.readRun.context receipt.readRun.contextKind)
    receipt.readDescriptor receipt.readRun.resolved receipt.readRun.prepared
    (.completed receipt.readRun.complete) receipt.readRun.contextKind receipt.readRun.cause
    receipt.read.writes receipt.readLedgerEffect receipt.readAuthorityEffect

theorem read_placement {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    ∃ base, receipt.readRun.resolved.allocation.base = some base ∧
      FitsAllocation base receipt.readRun.resolved.allocation.extent.stop ∧
      addressOf base receipt.readDescriptor.range.start =
        receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt := by
  obtain ⟨base, placed⟩ := receipt.readPlaced
  obtain ⟨fits, address⟩ := prepared_base_fits_and_address receipt.readRun.prepared placed
  exact ⟨base, placed, fits, Address.numeric.inj (address.symm.trans receipt.readAddress)⟩

theorem store_placement {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    ∃ base, receipt.storeRun.resolved.allocation.base = some base ∧
      FitsAllocation base receipt.storeRun.resolved.allocation.extent.stop ∧
      addressOf base receipt.storeDescriptor.range.start = before.gpr .rsp - 8 := by
  obtain ⟨base, placed⟩ := receipt.storePlaced
  obtain ⟨fits, address⟩ := prepared_base_fits_and_address receipt.storeRun.prepared placed
  exact ⟨base, placed, fits, Address.numeric.inj (address.symm.trans receipt.storeAddress)⟩

theorem rsp_exact {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    receipt.result.gpr .rsp = before.gpr .rsp - 8 := by simp [result, State.withGpr]

theorem rip_exact {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    receipt.result.rip = receipt.read.value := rfl

theorem rflags_exact {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    receipt.result.rflags = completedPushRflags before := rfl

theorem gpr_frame {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement)
    (register : Gpr) (other : register ≠ .rsp) :
    receipt.result.gpr register = before.gpr register := by
  simp [result, State.withGpr, other]

theorem read_event {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    ∃ valid, afterRead.events = afterFetch.events ++ [valid] ∧
      valid.event.valueRead = some receipt.read.observed := by
  obtain ⟨_, valid, _, event, appended, _, _, _⟩ := receipt.readRun.completed_event
  have fields := completedEvent_fields event
  exact ⟨valid, appended, fields.2.2.2.2.2.2.2.1.trans receipt.read.observed_exact⟩

theorem stored_event {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    ∃ valid, afterStore.events = afterRead.events ++ [valid] ∧
      valid.event.valueWritten = some (le64 receipt.fetch.site.fallthroughRip) := by
  obtain ⟨_, valid, _, event, appended, _, _, _⟩ := receipt.storeRun.completed_event
  have fields := completedEvent_fields event
  exact ⟨valid, appended, fields.2.2.2.2.2.2.2.2.trans receipt.written_exact⟩

theorem events_exact {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    ∃ fetched target saved,
      receipt.result.machine.events = before.machine.events ++ [fetched, target, saved] ∧
      fetched.event.valueRead = some receipt.fetch.site.encoding.toBytes ∧
      target.event.valueRead = some receipt.read.observed ∧
      saved.event.valueWritten = some (le64 receipt.fetch.site.fallthroughRip) := by
  obtain ⟨fetched, fetchEvents, fetchBytes, _⟩ := receipt.fetch.completed_event
  obtain ⟨target, readEvents, readBytes⟩ := receipt.read_event
  obtain ⟨saved, storeEvents, savedBytes⟩ := receipt.stored_event
  refine ⟨fetched, target, saved, ?_, fetchBytes, readBytes, savedBytes⟩
  change afterStore.events = _
  rw [storeEvents, readEvents, fetchEvents]
  simp [List.append_assoc]

theorem obligations_frame {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement) :
    receipt.result.machine.obligations = before.machine.obligations := by
  change afterStore.obligations = _
  rw [receipt.storeRun.prepared_result]
  exact (performPreparedAccess_noLedgerEffect_obligations receipt.storeRun.policy
    (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind)
    receipt.storeDescriptor receipt.storeRun.resolved receipt.storeRun.prepared
    (.completed receipt.storeRun.complete) receipt.storeRun.contextKind receipt.storeRun.cause
    receipt.storeLedgerEffect).trans
      (receipt.read_state_frame.2.trans receipt.fetch.state_frame.2)

end CallNormal
end Grass.ISA.X86.Execution
