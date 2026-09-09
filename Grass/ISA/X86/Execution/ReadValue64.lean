import Grass.ISA.X86.EndianBridge
import Grass.ISA.X86.Execution.AccessRun
import Grass.Op.ReadCompletion

/-!
# Exact QWORD values from completed reads
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86

/-- Evidence that an exact access run was an eight-byte initialized memory read
answered by the concrete memory oracle. -/
structure ReadValue64 {before after : MachineState} {descriptor : AccessDescriptor}
    (run : AccessRun before after descriptor) where
  writeData : MachineState → AccessDescriptor → ByteSeq
  indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte
  memoryOracle : run.policy.oracle = Oracle.ofMemory writeData indeterminate
  reads : descriptor.intent.reads = true
  writes : descriptor.intent.writes = false
  width : descriptor.range.size = 8
  initialization : descriptor.initialization = .allBytesInitialized

namespace ReadValue64

def observed {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) : ByteSeq :=
  run.complete.committed.observed.get
    (run.complete.committed.observedPresent read.reads)

theorem observed_exact {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    run.complete.committed.observed = some read.observed :=
  (Option.some_get (run.complete.committed.observedPresent read.reads)).symm

theorem observed_width {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    read.observed.length = 8 := by
  obtain ⟨bytes, observedBytes, bytesLength, _⟩ :=
    Grass.Op.CompleteCommitted.readOnly_bytes run.complete read.reads read.writes
  have same : read.observed = bytes := by
    apply Option.some.inj
    exact read.observed_exact.symm.trans observedBytes
  rw [same, bytesLength, read.width]

def bytes {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    Grass.Grammar.SizedByteArray 8 :=
  ⟨Vec.fromList read.observed, by simp [read.observed_width]⟩

@[simp] theorem bytes_toList {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    read.bytes.1.toList = read.observed := by
  simp [bytes]

def value {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) : BitVec 64 :=
  Grass.Grammar.littleEndianToBitVec read.bytes

theorem observed_backing {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    read.observed = observedBytes run.resolved
      (read.indeterminate (before.noteContext run.context run.contextKind) descriptor) := by
  have answer : (Oracle.ofMemory read.writeData read.indeterminate).answerResolved
      (before.noteContext run.context run.contextKind) descriptor run.resolved =
        some run.complete := by
    rw [← read.memoryOracle]
    exact run.answerResolved
  have exactBacking := Oracle.ofMemory_observed_of_answerResolved
    read.writeData read.indeterminate
    (before.noteContext run.context run.contextKind) descriptor run.resolved
    run.complete answer read.reads
  exact Option.some.inj (read.observed_exact.symm.trans exactBacking)

theorem initialized {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    run.resolved.RangeInitialized :=
  rangeInitialized_of_prepareAccess_allBytesInitialized run.prepared read.initialization

theorem value_of_observed_eq_le64 {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue64 run) (input : BitVec 64)
    (actual : run.complete.committed.observed = some (le64 input)) :
    read.value = input := by
  have observedEq : read.observed = le64 input := by
    apply Option.some.inj
    exact read.observed_exact.symm.trans actual
  have bytesEq : read.bytes = @Grass.Grammar.bitVecToLittleEndian 8 input := by
    apply Grass.Grammar.SizedVec.ext
    rw [← le64_toLittleEndian input]
    apply Vec.toList_injective
    rw [read.bytes_toList, observedEq]
  unfold value
  rw [bytesEq]
  exact @Grass.Grammar.littleEndianToBitVec_bitVecToLittleEndian 8 input

end ReadValue64
end Grass.ISA.X86.Execution
