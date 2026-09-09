import Grass.ISA.X86.Execution.PushNormal
import Grass.ISA.X86.Execution.ReadValue64
import Grass.Op.ReadBytes

/-!
# Immediate checked reads of values saved by a normal PUSH

This receipt connects the state produced by one actual normal PUSH store to an
actual, separate neutral read of that same saved span. It makes no claim about
later intervening writes, unwinding, or POP.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86

/-- An actual initialized QWORD read of the exact stack span just written by a
normal register PUSH. The read has its own logical cause. -/
structure PushSavedRead {before : State} {afterFetch afterStore afterRead : MachineState}
    {register : Gpr} (push : PushNormal before afterFetch afterStore register) where
  descriptor : AccessDescriptor
  read : AccessRun afterStore afterRead descriptor
  intent : descriptor.intent = .read
  /-- The read retains the PUSH policy except for its independently fixed oracle. -/
  policy : read.policy = { push.store.policy with oracle := read.policy.oracle }
  contextExact : descriptor.context = read.context
  contextKind : read.contextKind = push.store.contextKind
  root : descriptor.provenance.root = push.descriptor.provenance.root
  range : descriptor.range = push.descriptor.range
  address : descriptor.address = push.descriptor.address
  ordering : descriptor.ordering = .plain
  ledgerEffect : descriptor.ledgerEffect = []
  authorityEffect : descriptor.authorityEffect = []
  valueRead : ReadValue64 read

namespace PushSavedRead

/-- The exact post-store backing cells supply the actual read observation. -/
theorem observed_eq_le64 {before : State} {afterFetch afterStore afterRead : MachineState}
    {register : Gpr} (push : PushNormal before afterFetch afterStore register)
    (receipt : PushSavedRead (afterRead := afterRead) push) :
    receipt.valueRead.observed = le64 (before.gpr register) := by
  rw [receipt.valueRead.observed_backing]
  apply observedBytes_eq_of_state_cells receipt.read.resolved
    (le64 (before.gpr register))
  · simp [receipt.range, push.extent]
  · intro offset covered
    have pushCovered : push.descriptor.range.Covers offset := by
      simpa [receipt.range] using covered
    have saved := push.saved_cell offset pushCovered
    simpa [receipt.root, receipt.range] using saved

/-- Little-endian decoding of the observed saved bytes recovers the pre-PUSH GPR. -/
theorem value_exact {before : State} {afterFetch afterStore afterRead : MachineState}
    {register : Gpr} (push : PushNormal before afterFetch afterStore register)
    (receipt : PushSavedRead (afterRead := afterRead) push) :
    receipt.valueRead.value = before.gpr register := by
  apply receipt.valueRead.value_of_observed_eq_le64
  rw [receipt.valueRead.observed_exact, receipt.observed_eq_le64]

/-- The actual read appends an eight-byte completed read event carrying the
saved pre-PUSH register payload. -/
theorem read_event {before : State} {afterFetch afterStore afterRead : MachineState}
    {register : Gpr} (push : PushNormal before afterFetch afterStore register)
    (receipt : PushSavedRead (afterRead := afterRead) push) :
    ∃ valid, afterRead.events = afterStore.events ++ [valid] ∧
      valid.event.valueRead = some (le64 (before.gpr register)) ∧
      valid.event.status = .completed 8 0 := by
  obtain ⟨space, valid, _, event, appended, _, _, _⟩ := receipt.read.completed_event
  have fields := completedEvent_fields event
  have count := receipt.read.complete.readsFull receipt.valueRead.reads
  have zero : receipt.read.complete.committed.writeCount = 0 := by
    simp [Committed.writeCount,
      receipt.read.complete.committed.writtenAbsent receipt.valueRead.writes]
  refine ⟨valid, appended, ?_, ?_⟩
  · exact fields.2.2.2.2.2.2.2.1.trans receipt.valueRead.observed_exact |>.trans
      (by rw [receipt.observed_eq_le64])
  · simpa [count, zero, receipt.valueRead.width] using fields.2.2.2.2.2.2.1

/-- `read_frame` preserves the post-store memory and obligations for a neutral completed read. -/
theorem read_frame {before : State} {afterFetch afterStore afterRead : MachineState}
    {register : Gpr} (push : PushNormal before afterFetch afterStore register)
    (receipt : PushSavedRead (afterRead := afterRead) push) :
    afterRead.memory = afterStore.memory ∧ afterRead.obligations = afterStore.obligations := by
  rw [receipt.read.prepared_result]
  exact performPreparedAccess_readOnly_noEffects_frame receipt.read.policy
    (afterStore.noteContext receipt.read.context receipt.read.contextKind) receipt.descriptor
    receipt.read.resolved receipt.read.prepared (.completed receipt.read.complete)
    receipt.read.contextKind receipt.read.cause receipt.valueRead.writes receipt.ledgerEffect
    receipt.authorityEffect

end PushSavedRead
end Grass.ISA.X86.Execution
