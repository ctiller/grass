import Grass.ISA.X86.EndianBridge
import Grass.ISA.X86.Execution.AccessRun
import Grass.Op.ReadCompletion

/-!
# Exact DWORD values from completed frame reads

`ReadValue32` packages the shape of one actual, initialized, read-only
four-byte `AccessRun`. Its value is decoded from the completion's present
observation. This module does not connect that value to a source frame or give
it any instruction-level register effect.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution

/-- Evidence that an exact access run was a four-byte initialized memory read
answered by the concrete memory oracle. -/
structure ReadValue32 {before after : MachineState} {descriptor : AccessDescriptor}
    (run : AccessRun before after descriptor) where
  writeData : MachineState → AccessDescriptor → ByteSeq
  indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte
  memoryOracle : run.policy.oracle = Oracle.ofMemory writeData indeterminate
  reads : descriptor.intent.reads = true
  writes : descriptor.intent.writes = false
  width : descriptor.range.size = 4
  initialization : descriptor.initialization = .allBytesInitialized

namespace ReadValue32

/-- The bytes actually carried by the completed read. The proof supplied to
`Option.get` comes from the completed access itself. -/
def observed {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run) : ByteSeq :=
  run.complete.committed.observed.get
    (run.complete.committed.observedPresent read.reads)

/-- The completion's observation is exactly the proof-extracted byte sequence. -/
theorem observed_exact {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run) :
    run.complete.committed.observed = some read.observed := by
  exact (Option.some_get
    (run.complete.committed.observedPresent read.reads)).symm

/-- The proof-extracted observation has DWORD width. -/
theorem observed_width {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run) :
    read.observed.length = 4 := by
  obtain ⟨bytes, observedBytes, bytesLength, _⟩ :=
    Grass.Op.CompleteCommitted.readOnly_bytes run.complete read.reads read.writes
  have same : read.observed = bytes := by
    apply Option.some.inj
    exact read.observed_exact.symm.trans observedBytes
  rw [same, bytesLength, read.width]

/-- The fixed-width representation of the exact completed observation. -/
def bytes {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run) :
    Grass.Grammar.SizedByteArray 4 :=
  ⟨Vec.fromList read.observed, by simp [read.observed_width]⟩

/-- Forgetting the width proof recovers the exact observed byte sequence. -/
@[simp] theorem bytes_toList {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run) :
    read.bytes.1.toList = read.observed := by
  simp [bytes]

/-- The DWORD decoded in little-endian order from the exact completed bytes. -/
def value {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run) : BitVec 32 :=
  Grass.Grammar.littleEndianToBitVec read.bytes

/-- The concrete memory oracle observed exactly the resolved backing bytes at
the context-noted pre-state used by the access run. -/
theorem observed_backing {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run) :
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

/-- Preparation certifies initialization of the exact resolved backing span. -/
theorem initialized {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run) :
    run.resolved.RangeInitialized :=
  rangeInitialized_of_prepareAccess_allBytesInitialized run.prepared read.initialization

/-- If the actual observed bytes are x86's `le32` representation of a DWORD,
the value decoded through the grammar's little-endian representation is that
DWORD. -/
theorem value_of_observed_eq_le32 {before after : MachineState}
    {descriptor : AccessDescriptor} {run : AccessRun before after descriptor}
    (read : ReadValue32 run) (input : BitVec 32)
    (actual : run.complete.committed.observed = some (le32 input)) :
    read.value = input := by
  have observedEq : read.observed = le32 input := by
    apply Option.some.inj
    exact read.observed_exact.symm.trans actual
  have bytesEq : read.bytes = @Grass.Grammar.bitVecToLittleEndian 4 input := by
    apply Grass.Grammar.SizedVec.ext
    rw [← le32_toLittleEndian input]
    apply Vec.toList_injective
    rw [read.bytes_toList, observedEq]
  unfold value
  rw [bytesEq]
  exact @Grass.Grammar.littleEndianToBitVec_bitVecToLittleEndian 4 input

end ReadValue32
end Grass.ISA.X86.Execution
