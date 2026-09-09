import Grass.ISA.X86.Execution.MemoryAccess
import Grass.Op.WriteCompletion

/-! Values and backing updates derived from an actual continuous frame store.
The oracle payload is constrained at the actual context-noted pre-state. -/

namespace Grass.ISA.X86.Execution
open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution

namespace MemoryAccess

/-- `written_exact` derives the complete byte payload from the concrete oracle
answer, rather than asking the caller to provide a matching completion. -/
theorem written_exact {before : State} {afterFetch after : MachineState}
    {fetch : FetchedSite before afterFetch} (access : MemoryAccess fetch after)
    (payload : ByteSeq) (intent : access.descriptor.intent = .write)
    (width : payload.length = access.descriptor.range.size)
    (supplied : fetch.writeData
      (afterFetch.noteContext access.run.context access.run.contextKind) access.descriptor = payload) :
    access.run.complete.committed.written = some payload := by
  have answer : (Oracle.ofMemory fetch.writeData fetch.indeterminate).answerResolved
      (afterFetch.noteContext access.run.context access.run.contextKind)
      access.descriptor access.run.resolved = some access.run.complete := by
    rw [← access.memoryOracle]
    exact access.run.answerResolved
  have written := Oracle.ofMemory_written_of_answerResolved fetch.writeData fetch.indeterminate
    (afterFetch.noteContext access.run.context access.run.contextKind)
    access.descriptor access.run.resolved access.run.complete answer (by rw [intent]; rfl)
  simpa only [supplied, ← width, List.take_length] using written

/-- `memory_committed` identifies the actual post-memory with the commit of the
actual prepared completion, retaining the exact backing-resolution witness. -/
theorem memory_committed {before : State} {afterFetch after : MachineState}
    {fetch : FetchedSite before afterFetch} (access : MemoryAccess fetch after) :
    after.memory =
      (afterFetch.noteContext access.run.context access.run.contextKind).memory.commitResolved
        access.descriptor access.run.resolved access.run.complete.committed.written
        access.run.complete.committed.writtenFits := by
  obtain ⟨space, found, wellFormed⟩ := access.run.wellFormed
  exact clean_prepared_complete_memory_eq_commitResolved access.run.policy
    (afterFetch.noteContext access.run.context access.run.contextKind) after access.descriptor
    access.run.resolved access.run.prepared access.run.complete access.run.contextKind
    access.run.cause space found wellFormed access.run.prepared_result access.run.clean
    access.ledgerEffect access.authorityEffect

/-- `obligations_frame` derives obligation preservation across fetch and data. -/
theorem obligations_frame {before : State} {afterFetch after : MachineState}
    {fetch : FetchedSite before afterFetch} (access : MemoryAccess fetch after) :
    after.obligations = before.machine.obligations := by
  rw [access.run.prepared_result]
  exact (performPreparedAccess_noLedgerEffect_obligations access.run.policy
    (afterFetch.noteContext access.run.context access.run.contextKind) access.descriptor
    access.run.resolved access.run.prepared (.completed access.run.complete)
    access.run.contextKind access.run.cause access.ledgerEffect).trans fetch.state_frame.2

end MemoryAccess
end Grass.ISA.X86.Execution
