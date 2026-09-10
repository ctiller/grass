import Grass.ISA.X86.EndianBridge
import Grass.Op.AccessRun
import Grass.Op.ReadObservation

/-!
# Exact values from completed x86 reads

`ReadValue count` packages an actual, initialized, read-only `AccessRun` and
decodes its completed observation as a count-byte little-endian x86 value.
-/

namespace Grass.ISA.X86.Execution

open Grass.Op.AccessFactory (AccessRun)
open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86

/-- Evidence that an exact access run is a `count`-byte initialized memory
read answered by its concrete memory oracle. -/
structure ReadValue (count : Nat) {before after : MachineState}
    {descriptor : AccessDescriptor} (run : AccessRun before after descriptor) where
  writeData : MachineState → AccessDescriptor → ByteSeq
  indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte
  memoryOracle : run.policy.oracle = Oracle.ofMemory writeData indeterminate
  reads : descriptor.intent.reads = true
  writes : descriptor.intent.writes = false
  width : descriptor.range.size = count
  initialization : descriptor.initialization = .allBytesInitialized

namespace ReadValue

def observed {count : Nat} {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue count run) : ByteSeq :=
  Grass.Op.AccessFactory.AccessRun.readBytes run read.reads

theorem observed_exact {count : Nat} {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue count run) :
    run.complete.committed.observed = some read.observed :=
  Grass.Op.AccessFactory.AccessRun.readBytes_exact run read.reads

theorem observed_width {count : Nat} {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue count run) : read.observed.length = count := by
  rw [observed, Grass.Op.AccessFactory.AccessRun.readBytes_length run read.reads, read.width]

def bytes {count : Nat} {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue count run) :
    Grass.Grammar.SizedByteArray count :=
  ⟨Vec.fromList read.observed, by simp [read.observed_width]⟩

@[simp] theorem bytes_toList {count : Nat} {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue count run) : read.bytes.1.toList = read.observed := by
  simp [bytes]

def value {count : Nat} {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue count run) : BitVec (8 * count) :=
  Grass.Grammar.littleEndianToBitVec read.bytes

theorem observed_backing {count : Nat} {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue count run) :
    read.observed = observedBytes run.resolved
      (read.indeterminate (before.noteContext run.context run.contextKind) descriptor) := by
  exact Grass.Op.AccessFactory.AccessRun.readBytes_backing run read.writeData read.indeterminate
    read.memoryOracle read.reads

theorem initialized {count : Nat} {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue count run) : run.resolved.RangeInitialized :=
  Grass.Op.AccessFactory.AccessRun.initialized run read.initialization

/-- Decoding the completed observation recovers any value whose canonical
little-endian bytes were observed. -/
theorem value_of_observed_eq_littleEndian {count : Nat} {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue count run) (input : BitVec (8 * count))
    (actual : run.complete.committed.observed =
      some (@Grass.Grammar.bitVecToLittleEndian count input).1.toList) :
    read.value = input := by
  have observedEq : read.observed = (@Grass.Grammar.bitVecToLittleEndian count input).1.toList := by
    apply Option.some.inj
    exact read.observed_exact.symm.trans actual
  have bytesEq : read.bytes = @Grass.Grammar.bitVecToLittleEndian count input := by
    apply Grass.Grammar.SizedVec.ext
    apply Vec.toList_injective
    rw [read.bytes_toList, observedEq]
  unfold value
  rw [bytesEq]
  exact @Grass.Grammar.littleEndianToBitVec_bitVecToLittleEndian count input

/-- x86's QWORD byte helper decodes through the shared little-endian value
view. -/
theorem value_of_observed_eq_le64 {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue 8 run) (input : BitVec 64)
    (actual : run.complete.committed.observed = some (le64 input)) :
    read.value = input := by
  have observedEq : read.observed = le64 input := by
    apply Option.some.inj
    exact read.observed_exact.symm.trans actual
  apply Grass.ISA.X86.littleEndianToBitVec_of_le64 read.bytes input
  rw [read.bytes_toList, observedEq]

end ReadValue
end Grass.ISA.X86.Execution
