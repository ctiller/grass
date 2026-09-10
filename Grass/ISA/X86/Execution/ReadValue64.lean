import Grass.ISA.X86.EndianBridge
import Grass.ISA.X86.Execution.AccessRun
import Grass.Op.ReadObservation

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
  Grass.Op.AccessFactory.AccessRun.readBytes run read.reads

theorem observed_exact {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    run.complete.committed.observed = some read.observed :=
  Grass.Op.AccessFactory.AccessRun.readBytes_exact run read.reads

theorem observed_width {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    read.observed.length = 8 := by
  rw [observed, Grass.Op.AccessFactory.AccessRun.readBytes_length run read.reads, read.width]

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
  exact Grass.Op.AccessFactory.AccessRun.readBytes_backing run read.writeData read.indeterminate read.memoryOracle read.reads

theorem initialized {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue64 run) :
    run.resolved.RangeInitialized :=
  Grass.Op.AccessFactory.AccessRun.initialized run read.initialization

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
