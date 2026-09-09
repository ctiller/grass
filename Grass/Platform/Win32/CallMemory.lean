import Grass.Op.CallProtocol

/-! Shared resolved memory coordinates for Win32 calls. -/
namespace Grass.Platform.Win32.CallMemory

open Grass.Core Grass.Memory Grass.Op

structure Argument where
  provenance : Provenance
  range : ByteRange
deriving DecidableEq, Repr

structure Resolved (memory : MemoryState) (arg : Argument)
    extends memory.ResolvedAccess arg.provenance arg.range where
  base : MachineAddress
  placed : allocation.base = some base
  noWrap : FitsAllocation base allocation.extent.stop

def Resolved.physical {memory : MemoryState} {arg : Argument}
    (resolved : Resolved memory arg) : ByteRange :=
  arg.range.shift resolved.base.toNat

theorem Resolved.root_contains {memory : MemoryState} {arg : Argument}
    (resolved : Resolved memory arg) : resolved.allocation.extent.Contains arg.range := by
  rw [resolved.extentAgrees]
  exact (Provenance.extent_within_root resolved.provenanceNested).trans resolved.rangeInProvenance

def Resolved.transport {before after : MemoryState} {arg : Argument}
    (resolved : Resolved before arg) (same : after.allocations = before.allocations)
    (backings : after.backings = before.backings) : Resolved after arg :=
  { toResolvedAccess := resolved.toResolvedAccess.transport same backings
    base := resolved.base, placed := resolved.placed, noWrap := resolved.noWrap }

end Grass.Platform.Win32.CallMemory
