import Grass.Op.AccessRun
import Grass.Op.ReadCompletion

/-!
# Observations from an actual access run

This module exposes the bytes already carried by a completed generic
`AccessRun`.  It adds no read engine and makes no assumption about an ISA,
register width, or byte order.  When the selected oracle is `Oracle.ofMemory`,
the laws below tie that actual completion directly to the run's resolved backing
observation.
-/

namespace Grass.Op.AccessFactory.AccessRun

open Grass.Core Grass.Memory Grass.Std.Logical

/-- The byte sequence present in the actual complete answer of a reading run. -/
def readBytes {before after : MachineState} {descriptor : AccessDescriptor}
    (run : AccessRun before after descriptor)
    (reads : descriptor.intent.reads = true) : ByteSeq :=
  run.complete.committed.observed.get
    (run.complete.committed.observedPresent reads)

/-- `readBytes_exact` recovers the exact observed field from which `readBytes`
was obtained. -/
@[simp] theorem readBytes_exact {before after : MachineState}
    {descriptor : AccessDescriptor} (run : AccessRun before after descriptor)
    (reads : descriptor.intent.reads = true) :
    run.complete.committed.observed = some (run.readBytes reads) :=
  (Option.some_get (run.complete.committed.observedPresent reads)).symm

/-- A complete reading run observes the descriptor's complete byte range. -/
@[simp] theorem readBytes_length {before after : MachineState}
    {descriptor : AccessDescriptor} (run : AccessRun before after descriptor)
    (reads : descriptor.intent.reads = true) :
    (run.readBytes reads).length = descriptor.range.size := by
  have full := run.complete.readsFull reads
  simpa [Committed.readCount, run.readBytes_exact reads] using full

/-- With the concrete memory oracle selected by the run, its actual completion
contains exactly the bytes observed through the run's resolved backing span. -/
theorem completion_observed_backing {before after : MachineState}
    {descriptor : AccessDescriptor} (run : AccessRun before after descriptor)
    (writeData : MachineState → AccessDescriptor → ByteSeq)
    (indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte)
    (oracleExact : run.policy.oracle = Oracle.ofMemory writeData indeterminate)
    (reads : descriptor.intent.reads = true) :
    run.complete.committed.observed =
      some (observedBytes run.resolved
        (indeterminate (before.noteContext run.context run.contextKind) descriptor)) := by
  apply Oracle.ofMemory_observed_of_answerResolved writeData indeterminate
    (before.noteContext run.context run.contextKind) descriptor run.resolved run.complete
  · rw [← oracleExact]
    exact run.answerResolved
  · exact reads

/-- `readBytes_backing` is the proof-consuming byte-sequence form of
`completion_observed_backing`. -/
theorem readBytes_backing {before after : MachineState}
    {descriptor : AccessDescriptor} (run : AccessRun before after descriptor)
    (writeData : MachineState → AccessDescriptor → ByteSeq)
    (indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte)
    (oracleExact : run.policy.oracle = Oracle.ofMemory writeData indeterminate)
    (reads : descriptor.intent.reads = true) :
    run.readBytes reads =
      observedBytes run.resolved
        (indeterminate (before.noteContext run.context run.contextKind) descriptor) := by
  apply Option.some.inj
  rw [← run.readBytes_exact reads]
  exact run.completion_observed_backing writeData indeterminate oracleExact reads

/-- A run admitted with the all-bytes-initialized demand carries initialization
evidence for its exact resolved range. -/
theorem initialized {before after : MachineState} {descriptor : AccessDescriptor}
    (run : AccessRun before after descriptor)
    (demand : descriptor.initialization = .allBytesInitialized) :
    run.resolved.RangeInitialized :=
  rangeInitialized_of_prepareAccess_allBytesInitialized run.prepared demand

end Grass.Op.AccessFactory.AccessRun
