import Grass.Platform.BareMetal.BootFetch

/-!
# AArch64 consumption of admitted physical boot bytes

The reader checks four-byte width and PC alignment before the shared execute
read. It returns the actual four bytes in address order, leaving instruction
decoding and byte-order interpretation to the AArch64 consumer. Exception level,
translation and firmware-entry applicability are external requirements.
-/

namespace Grass.Platform.BareMetal.AArch64BootFetch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical BootMemory

variable {map : PhysicalMap} {context : ContextId} {before : MachineState}
  {admission : Admission map context before} {id : AllocId} {range : ByteRange}

/-- An aligned four-byte observation obtained by the shared execute-read factory. -/
structure Word (policy : BootFetch.Policy) (entry : Entry admission id range) where
  read : BootFetch.Success policy entry
  width : range.size = 4
  aligned : entry.pc.toNat % 4 = 0

/-- Structural refusal is distinct from an actual operation-step failure. -/
inductive Failure (policy : BootFetch.Policy) (entry : Entry admission id range) where
  | width
  | alignment
  | access (reason : AccessFactory.AccessFailure (BootFetch.descriptor policy entry))

/-- `fetchWord` checks the AArch64 word shape before performing the shared read. -/
def fetchWord (policy : BootFetch.Policy) (entry : Entry admission id range) :
    Except (Failure policy entry) (Word policy entry) :=
  if width : range.size = 4 then
    if aligned : entry.pc.toNat % 4 = 0 then
      match BootFetch.fetch policy entry with
      | .error reason => .error (.access reason)
      | .ok read => .ok ⟨read, width, aligned⟩
    else .error .alignment
  else .error .width

/-- `bytes_length` derives four actual bytes from the completed memory read. -/
theorem Word.bytes_length {policy : BootFetch.Policy} {entry : Entry admission id range}
    (word : Word policy entry) : word.read.bytes.length = 4 :=
  word.read.bytes_length.trans word.width

end Grass.Platform.BareMetal.AArch64BootFetch
