import Grass.Platform.BareMetal.BootFetch
import Grass.ISA.X86.Execution.ObservedFetch

/-!
# x86-64 consumption of admitted physical boot bytes

The shared physical execute-read becomes the existing x86 observed-fetch
receipt at its exact PC. Canonical decoding consumes those observed bytes.
This adapter assumes a post-firmware x86-64 address regime applicable to the
physical snapshot; it does not model reset, paging setup or instruction transfer.
-/

namespace Grass.Platform.BareMetal.X86BootFetch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution BootMemory

variable {map : PhysicalMap} {context : ContextId} {before : MachineState}
  {admission : Admission map context before} {id : AllocId} {range : ByteRange}
  {policy : BootFetch.Policy} {entry : Entry admission id range}

/-- `state` embeds the admitted shared machine at the selected physical entry PC. -/
def state (entry : Entry admission id range) (gpr : Gpr → BitVec 64)
    (rflags : BitVec 64) : State :=
  { machine := admission.machine, gpr := gpr, rip := entry.pc, rflags := rflags }

/-- `observed` reuses the actual generic access receipt in the existing x86 path. -/
def observed (success : BootFetch.Success policy entry) (gpr : Gpr → BitVec 64)
    (rflags : BitVec 64) : ObservedFetch (state entry gpr rflags) success.after :=
  { descriptor := BootFetch.descriptor policy entry, run := success.run
    writeData := fun _ _ => [], indeterminate := fun _ _ _ => 0
    memoryOracle := by rw [success.policy_exact]; rfl
    intent := rfl, initialization := rfl, ledgerEffect := rfl, authorityEffect := rfl
    address := rfl, placed := ⟨entry.base, success.placed⟩ }

/-- `observed_bytes` ensures the ISA view has no independent byte source. -/
theorem observed_bytes (success : BootFetch.Success policy entry) (gpr : Gpr → BitVec 64)
    (rflags : BitVec 64) : (observed success gpr rflags).bytes = success.bytes := rfl

/-- `decode` applies the existing x86 decoder to the committed observation.
The result may retain trailing bytes; this is a byte-consumption adapter, not
an exact-footprint instruction execution theorem. -/
def decode (success : BootFetch.Success policy entry) :
    Except DecodedSite.Error (DecodedSite entry.pc success.bytes) :=
  DecodedSite.check entry.pc success.bytes

end Grass.Platform.BareMetal.X86BootFetch
