import Grass.ISA.X86.Execution.AccessRun
import Grass.ISA.X86.Execution.DecodedSite
import Grass.ISA.X86.Execution.State
import Grass.Op.ReadCompletion
import Grass.Op.PreparedPlacement

/-!
# Canonical instructions observed by actual execute accesses

A fetched site uses the bytes of the exact resolved memory-backed oracle answer.
Its fetch is a clean, initialized execute access at the architectural RIP with
a present allocation placement. Decoding consumes the whole observed extent.
This does not bind the bytes to an assembly source or execute their semantics.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

/-- A checked fetch and canonical decode over its actual backing observation.
The architectural input and resulting memory machine are explicit indices. -/
structure FetchedSite (before : State) (after : MachineState) where
  descriptor : AccessDescriptor
  run : AccessRun before.machine after descriptor
  writeData : MachineState → AccessDescriptor → ByteSeq
  indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte
  memoryOracle : run.policy.oracle = Oracle.ofMemory writeData indeterminate
  intent : descriptor.intent = .execute
  initialization : descriptor.initialization = .allBytesInitialized
  /-- Instruction fetch does not perform obligation transfers. -/
  ledgerEffect : descriptor.ledgerEffect = []
  /-- Instruction fetch does not perform authority transfers. -/
  authorityEffect : descriptor.authorityEffect = []
  address : descriptor.address = .numeric before.rip
  /-- CPU placement must exist; absent placement would skip its agreement check. -/
  placed : ∃ base, run.resolved.allocation.base = some base
  site : DecodedSite before.rip
    (observedBytes run.resolved
      (indeterminate (before.machine.noteContext run.context run.contextKind) descriptor))
  noTrailing : site.rest = []

namespace FetchedSite

/-- The present allocation base and successful preparation locate the read at RIP. -/
theorem placement {before : State} {after : MachineState}
    (fetch : FetchedSite before after) :
    ∃ base, fetch.run.resolved.allocation.base = some base ∧
      FitsAllocation base fetch.run.resolved.allocation.extent.stop ∧
      addressOf base fetch.descriptor.range.start = before.rip := by
  obtain ⟨base, placed⟩ := fetch.placed
  obtain ⟨fits, address⟩ := prepared_base_fits_and_address fetch.run.prepared placed
  refine ⟨base, placed, fits, ?_⟩
  exact Address.numeric.inj (address.symm.trans fetch.address)

/-- `afterState` replaces only the embedded memory machine. -/
def afterState {before : State} {after : MachineState}
    (_fetch : FetchedSite before after) : State := { before with machine := after }

/-- The actual oracle completion observed the backing bytes used by the decoder. -/
theorem observed_exact {before : State} {after : MachineState}
    (fetch : FetchedSite before after) :
    fetch.run.complete.committed.observed = some fetch.site.encoding.toBytes := by
  have answer : (Oracle.ofMemory fetch.writeData fetch.indeterminate).answerResolved
      (before.machine.noteContext fetch.run.context fetch.run.contextKind)
      fetch.descriptor fetch.run.resolved = some fetch.run.complete := by
    rw [← fetch.memoryOracle]
    exact fetch.run.answerResolved
  have observed := Oracle.ofMemory_observed_of_answerResolved fetch.writeData fetch.indeterminate
    (before.machine.noteContext fetch.run.context fetch.run.contextKind) fetch.descriptor
    fetch.run.resolved fetch.run.complete answer (by rw [fetch.intent]; rfl)
  rw [fetch.site.bytesExact, fetch.noTrailing, List.append_nil] at observed
  exact observed

/-- Fetch extent is derived from the observed bytes and complete decoding. -/
theorem extent_exact {before : State} {after : MachineState}
    (fetch : FetchedSite before after) : fetch.descriptor.range.size = fetch.site.encoding.size := by
  have lengths := congrArg List.length fetch.site.bytesExact
  simpa [observedBytes, fetch.noTrailing] using lengths

/-- Preparation certifies initialization of the exact fetched backing span. -/
theorem initialized {before : State} {after : MachineState}
    (fetch : FetchedSite before after) : fetch.run.resolved.RangeInitialized :=
  rangeInitialized_of_prepareAccess_allBytesInitialized fetch.run.prepared fetch.initialization

/-- `state_frame` derives memory and obligation preservation from the neutral read. -/
theorem state_frame {before : State} {after : MachineState}
    (fetch : FetchedSite before after) :
    after.memory = before.machine.memory ∧ after.obligations = before.machine.obligations := by
  have actual := ran_singleton_prepared_eq_performPreparedAccess fetch.run.policy before.machine
    fetch.run.operation fetch.run.context fetch.run.contextKind fetch.run.cause fetch.run.faultAt
    fetch.run.sequence fetch.descriptor after fetch.run.selected fetch.run.accesses_exact
    fetch.run.noFault fetch.run.ran fetch.run.resolved fetch.run.prepared fetch.run.complete
    fetch.run.answerResolved
  rw [actual]
  exact performPreparedAccess_readOnly_noEffects_frame fetch.run.policy
    (before.machine.noteContext fetch.run.context fetch.run.contextKind) fetch.descriptor
    fetch.run.resolved fetch.run.prepared (.completed fetch.run.complete) fetch.run.contextKind
    fetch.run.cause (by rw [fetch.intent]; rfl) fetch.ledgerEffect fetch.authorityEffect

/-- `storage_frame` projects the full memory frame to its backing and allocation tables. -/
theorem storage_frame {before : State} {after : MachineState}
    (fetch : FetchedSite before after) :
    after.memory.allocations = before.machine.memory.allocations ∧
      after.memory.backings = before.machine.memory.backings := by
  rw [fetch.state_frame.1]
  exact ⟨rfl, rfl⟩

/-- The actual fetch event records precisely the bytes accepted by the decoder. -/
theorem completed_event {before : State} {after : MachineState}
    (fetch : FetchedSite before after) :
    ∃ valid, after.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some fetch.site.encoding.toBytes ∧
      valid.event.status = .completed fetch.site.encoding.size 0 := by
  obtain ⟨space, valid, _, event, appended, _, _, _⟩ := fetch.run.completed_event
  have fields := completedEvent_fields event
  have reads : fetch.descriptor.intent.reads = true := by rw [fetch.intent]; rfl
  have writes : fetch.descriptor.intent.writes = false := by rw [fetch.intent]; rfl
  have count := fetch.run.complete.readsFull reads
  have zero : fetch.run.complete.committed.writeCount = 0 := by
    simp [Committed.writeCount, fetch.run.complete.committed.writtenAbsent writes]
  refine ⟨valid, appended, ?_, ?_⟩
  · exact fields.2.2.2.2.2.2.2.1.trans fetch.observed_exact
  · simpa [count, zero, fetch.extent_exact] using fields.2.2.2.2.2.2.1

end FetchedSite
end Grass.ISA.X86.Execution
