import Grass.ISA.X86.Execution.PushNormal
import Grass.ISA.X86.Execution.CallNormal

/-! Frame authoritative code allocations and cells across actual stack writes.
The write root must be distinct from the observed code root; no whole-memory
equality or postulated post-write cell equality is used. -/

namespace Grass.Assembly.CodeWriteFrame

open Grass.Memory Grass.ISA.X86 Grass.ISA.X86.Execution

/-- `push_allocation` preserves every allocation record across an actual PUSH. -/
theorem push_allocation {before : State} {afterFetch afterStore : MachineState}
    {register : Gpr} (receipt : PushNormal before afterFetch afterStore register)
    {code : AllocId} {record : AllocationRecord}
    (present : before.machine.memory.allocations.lookup code = some record) :
    afterStore.memory.allocations.lookup code = some record := by
  have fetchMemory :
      (afterFetch.noteContext receipt.store.context receipt.store.contextKind).memory =
        before.machine.memory := by
    exact receipt.fetch.state_frame.1
  rw [receipt.memory_written]
  simp only [MemoryState.allocations_writeResolved]
  rw [fetchMemory]
  exact present

/-- A PUSH stack write frames an allocation-local code cell when the actual
write provenance has a distinct root. -/
theorem push_cell {before : State} {afterFetch afterStore : MachineState}
    {register : Gpr} (receipt : PushNormal before afterFetch afterStore register)
    (dedicated : before.machine.memory.DedicatedBackings)
    {code : AllocId} (distinct : receipt.descriptor.provenance.root ≠ code)
    (offset : Nat) :
    afterStore.memory.cellAt? code offset = before.machine.memory.cellAt? code offset := by
  have fetchMemory :
      (afterFetch.noteContext receipt.store.context receipt.store.contextKind).memory =
        before.machine.memory := by
    exact receipt.fetch.state_frame.1
  rw [receipt.memory_written]
  calc
    _ = (afterFetch.noteContext receipt.store.context receipt.store.contextKind).memory.cellAt?
        code offset := by
      apply MemoryState.cellAt?_writeResolved_of_untouched
      · rw [fetchMemory]
        exact dedicated
      · intro touched
        exact distinct touched.1
    _ = _ := by rw [fetchMemory]

/-- `call_allocation` preserves every allocation record across the actual CALL write. -/
theorem call_allocation {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement)
    {code : AllocId} {record : AllocationRecord}
    (present : before.machine.memory.allocations.lookup code = some record) :
    afterStore.memory.allocations.lookup code = some record := by
  have readMemory :
      (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind).memory =
        before.machine.memory := by
    exact receipt.read_state_frame.1.trans receipt.fetch.state_frame.1
  rw [receipt.memory_written]
  simp only [MemoryState.allocations_writeResolved]
  rw [readMemory]
  exact present

/-- A CALL return-address write frames a code cell at a distinct actual root;
the preceding target read is framed by the read-only execution law. -/
theorem call_cell {before : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    (receipt : CallNormal before afterFetch afterRead afterStore displacement)
    (dedicated : before.machine.memory.DedicatedBackings)
    {code : AllocId} (distinct : receipt.storeDescriptor.provenance.root ≠ code)
    (offset : Nat) :
    afterStore.memory.cellAt? code offset = before.machine.memory.cellAt? code offset := by
  have readMemory :
      (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind).memory =
        before.machine.memory := by
    exact receipt.read_state_frame.1.trans receipt.fetch.state_frame.1
  rw [receipt.memory_written]
  calc
    _ = (afterRead.noteContext receipt.storeRun.context receipt.storeRun.contextKind).memory.cellAt?
        code offset := by
      apply MemoryState.cellAt?_writeResolved_of_untouched
      · rw [readMemory]
        exact dedicated
      · intro touched
        exact distinct touched.1
    _ = _ := by rw [readMemory]

end Grass.Assembly.CodeWriteFrame
