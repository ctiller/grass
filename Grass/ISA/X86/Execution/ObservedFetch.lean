import Grass.ISA.X86.Execution.Fetch
import Grass.ISA.X86.Execution.FetchAttempt

/-!
# Actual instruction-byte observations before decoding

`ObservedFetch` records a completed, clean execute read at architectural RIP.
It intentionally carries no decoder success, instruction classification, or
fallthrough claim.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

/-- A source-free actual execute-read observation, before any instruction bytes
are required to decode. -/
structure ObservedFetch (before : State) (after : MachineState) where
  descriptor : AccessDescriptor
  run : AccessRun before.machine after descriptor
  writeData : MachineState → AccessDescriptor → ByteSeq
  indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte
  memoryOracle : run.policy.oracle = Oracle.ofMemory writeData indeterminate
  intent : descriptor.intent = .execute
  initialization : descriptor.initialization = .allBytesInitialized
  ledgerEffect : descriptor.ledgerEffect = []
  authorityEffect : descriptor.authorityEffect = []
  address : descriptor.address = .numeric before.rip
  placed : ∃ base, run.resolved.allocation.base = some base

namespace ObservedFetch

/-- The exact backing observation supplied to the memory oracle. -/
def bytes {before : State} {after : MachineState}
    (fetch : ObservedFetch before after) : ByteSeq :=
  observedBytes fetch.run.resolved
    (fetch.indeterminate (before.machine.noteContext fetch.run.context fetch.run.contextKind)
      fetch.descriptor)

theorem placement {before : State} {after : MachineState}
    (fetch : ObservedFetch before after) :
    ∃ base, fetch.run.resolved.allocation.base = some base ∧
      FitsAllocation base fetch.run.resolved.allocation.extent.stop ∧
      addressOf base fetch.descriptor.range.start = before.rip := by
  obtain ⟨base, placed⟩ := fetch.placed
  obtain ⟨fits, address⟩ := prepared_base_fits_and_address fetch.run.prepared placed
  refine ⟨base, placed, fits, ?_⟩
  exact Address.numeric.inj (address.symm.trans fetch.address)

theorem initialized {before : State} {after : MachineState}
    (fetch : ObservedFetch before after) : fetch.run.resolved.RangeInitialized :=
  rangeInitialized_of_prepareAccess_allBytesInitialized fetch.run.prepared fetch.initialization

theorem state_frame {before : State} {after : MachineState}
    (fetch : ObservedFetch before after) :
    after.memory = before.machine.memory ∧ after.obligations = before.machine.obligations := by
  rw [fetch.run.prepared_result]
  exact performPreparedAccess_readOnly_noEffects_frame fetch.run.policy
    (before.machine.noteContext fetch.run.context fetch.run.contextKind) fetch.descriptor
    fetch.run.resolved fetch.run.prepared (.completed fetch.run.complete) fetch.run.contextKind
    fetch.run.cause (by rw [fetch.intent]; rfl) fetch.ledgerEffect fetch.authorityEffect

theorem observed_exact {before : State} {after : MachineState}
    (fetch : ObservedFetch before after) :
    fetch.run.complete.committed.observed = some fetch.bytes := by
  have answer : (Oracle.ofMemory fetch.writeData fetch.indeterminate).answerResolved
      (before.machine.noteContext fetch.run.context fetch.run.contextKind)
      fetch.descriptor fetch.run.resolved = some fetch.run.complete := by
    rw [← fetch.memoryOracle]
    exact fetch.run.answerResolved
  exact Oracle.ofMemory_observed_of_answerResolved fetch.writeData fetch.indeterminate
    (before.machine.noteContext fetch.run.context fetch.run.contextKind) fetch.descriptor
    fetch.run.resolved fetch.run.complete answer (by rw [fetch.intent]; rfl)

theorem completed_event {before : State} {after : MachineState}
    (fetch : ObservedFetch before after) :
    ∃ valid, after.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some fetch.bytes ∧
      valid.event.status = .completed fetch.descriptor.range.size 0 := by
  obtain ⟨space, valid, _, event, appended, _, _, _⟩ := fetch.run.completed_event
  have fields := completedEvent_fields event
  have reads : fetch.descriptor.intent.reads = true := by rw [fetch.intent]; rfl
  have writes : fetch.descriptor.intent.writes = false := by rw [fetch.intent]; rfl
  have count := fetch.run.complete.readsFull reads
  have zero : fetch.run.complete.committed.writeCount = 0 := by
    simp [Committed.writeCount, fetch.run.complete.committed.writtenAbsent writes]
  refine ⟨valid, appended, fields.2.2.2.2.2.2.2.1.trans fetch.observed_exact, ?_⟩
  simpa [count, zero] using fields.2.2.2.2.2.2.1

end ObservedFetch

namespace FetchedSite

/-- Forget the successful decode while retaining the same actual raw read receipt. -/
def toObservedFetch {before : State} {after : MachineState}
    (fetch : FetchedSite before after) : ObservedFetch before after where
  descriptor := fetch.descriptor
  run := fetch.run
  writeData := fetch.writeData
  indeterminate := fetch.indeterminate
  memoryOracle := fetch.memoryOracle
  intent := fetch.intent
  initialization := fetch.initialization
  ledgerEffect := fetch.ledgerEffect
  authorityEffect := fetch.authorityEffect
  address := fetch.address
  placed := fetch.placed

/-- The raw receipt observes exactly the bytes accepted by the checked decoder. -/
theorem toObservedFetch_bytes {before : State} {after : MachineState}
    (fetch : FetchedSite before after) :
    fetch.toObservedFetch.bytes = fetch.site.encoding.toBytes := by
  have raw := fetch.toObservedFetch.observed_exact
  have decoded := fetch.observed_exact
  exact Option.some.inj (raw.symm.trans decoded)

end FetchedSite

namespace ObservedFetch

/-- A raw successful observation is also an actual running fetch attempt when
the descriptor's context is supplied explicitly. No decoder fact is used. -/
def toFetchAttempt {before : State} {after : MachineState}
    (fetch : ObservedFetch before after)
    (contextExact : fetch.descriptor.context = fetch.run.context) :
    FetchAttempt before (.ran after) where
  policy := fetch.run.policy
  operation := fetch.run.operation
  context := fetch.run.context
  contextKind := fetch.run.contextKind
  cause := fetch.run.cause
  faultAt := fetch.run.faultAt
  descriptor := fetch.descriptor
  sequence := fetch.run.sequence
  selected := fetch.run.selected
  substeps_exact := fetch.run.substeps_exact
  contextExact := contextExact
  intent := fetch.intent
  initialization := fetch.initialization
  ledgerEffect := fetch.ledgerEffect
  authorityEffect := fetch.authorityEffect
  address := fetch.address
  actual := fetch.run.ran

end ObservedFetch
end Grass.ISA.X86.Execution
