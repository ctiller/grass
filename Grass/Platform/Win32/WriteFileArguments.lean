import Grass.Op.CallProtocol
import Grass.Std.Logical.Vec
import Grass.Platform.Win32.CallMemory

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

abbrev Argument := Grass.Platform.Win32.CallMemory.Argument

/-- Resolve against the actual live allocation, retaining the lookup and placement.
This supplies spatial evidence only, never access rights. -/
abbrev Resolved := Grass.Platform.Win32.CallMemory.Resolved

abbrev Resolved.physical {memory : MemoryState} {arg : Argument}
    (resolved : Resolved memory arg) :=
  Grass.Platform.Win32.CallMemory.Resolved.physical resolved

theorem Resolved.root_contains {memory : MemoryState} {arg : Argument}
    (resolved : Resolved memory arg) : resolved.allocation.extent.Contains arg.range :=
  Grass.Platform.Win32.CallMemory.Resolved.root_contains resolved

def Resolved.transport {before after : MemoryState} {arg : Argument}
    (resolved : Resolved before arg) (same : after.allocations = before.allocations)
    (backings : after.backings = before.backings) : Resolved after arg :=
  Grass.Platform.Win32.CallMemory.Resolved.transport resolved same backings

structure Request where
  handle : BitVec 64
  requested : BitVec 32
  buffer : Argument
  countSlot : Argument
  bytes : Vec Byte

def Request.loans (request : Request) : List CallProtocol.LoanRequest :=
  [⟨.loan, request.buffer.provenance, request.buffer.range, .readOnly⟩,
   ⟨.loan, request.countSlot.provenance, request.countSlot.range, { write := true }⟩]

/-- Snapshot correspondence includes initialization, not merely byte equality. -/
def InputMatches (memory : MemoryState) (request : Request) : Prop :=
  ∀ i : Fin request.bytes.length,
    memory.cellAt? request.buffer.provenance.root (request.buffer.range.start + i.val) =
      some (request.bytes.toList[i.val]'i.isLt, true)

instance (memory : MemoryState) (request : Request) : Decidable (InputMatches memory request) :=
  by unfold InputMatches; infer_instance

structure Prepared (memory : MemoryState) (request : Request) where
  buffer : Resolved memory request.buffer
  countSlot : Resolved memory request.countSlot
  bufferSize : request.buffer.range.size = request.requested.toNat
  bytesSize : request.bytes.length = request.requested.toNat
  countSize : request.countSlot.range.size = 4
  bufferCPU : request.buffer.provenance.space = .cpuVirtual
  countCPU : request.countSlot.provenance.space = .cpuVirtual
  separated : buffer.physical.Disjoint countSlot.physical
  dedicated : memory.DedicatedBackings
  placement : ∀ root allocation, memory.allocations.lookup root = some allocation →
    allocation.live = true → allocation.space = .cpuVirtual →
    ∃ base, allocation.base = some base ∧ FitsAllocation base allocation.extent.stop
  allocationSeparation : ∀ left right a b leftBase rightBase,
    memory.allocations.lookup left = some a → memory.allocations.lookup right = some b →
    left ≠ right → a.live = true → b.live = true →
    a.space = .cpuVirtual → b.space = .cpuVirtual →
    a.base = some leftBase → b.base = some rightBase →
    (a.extent.shift leftBase.toNat).Disjoint (b.extent.shift rightBase.toNat)
  input : InputMatches memory request

def Prepared.transport {before after : MemoryState} {request : Request}
    (prepared : Prepared before request) (same : after.allocations = before.allocations)
    (backings : after.backings = before.backings) : Prepared after request where
  buffer := prepared.buffer.transport same backings
  countSlot := prepared.countSlot.transport same backings
  bufferSize := prepared.bufferSize
  bytesSize := prepared.bytesSize
  countSize := prepared.countSize
  bufferCPU := prepared.bufferCPU
  countCPU := prepared.countCPU
  separated := prepared.separated
  dedicated := by
    unfold MemoryState.DedicatedBackings MemoryState.backingCapacity?
    rw [same, backings]
    exact prepared.dedicated
  placement := by rw [same]; exact prepared.placement
  allocationSeparation := by rw [same]; exact prepared.allocationSeparation
  input := by
    intro i
    rw [MemoryState.cellAt?_of_maps_eq same backings]
    exact prepared.input i

end Grass.Platform.Win32.WriteFile
