import Grass.Assembly.FrameAddressing
import Grass.Assembly.SourceStore

/-! A placed, live allocation exercises the frame-address bridge through
`MemoryState.addressAt?`.  The local address is produced by the resolver, and
the frame base is deliberately nonzero; no derived displacement is copied into
the fixture. -/

namespace Grass.Tests.Assembly.FrameAddressing

open Grass.Assembly Grass.Core Grass.Memory Grass.Std.Logical

private def alloc : AllocId := (FreshSupply.initial (Tag := AllocTag)).fresh.1
private def epoch : EpochId := (FreshSupply.initial (Tag := EpochTag)).fresh.1
private def owner : ContextId := (FreshSupply.initial (Tag := ContextTag)).fresh.1

def rootOffset : Nat := 16
def frameLayout := SourceStore.frameForSlots 5 [] ["slot"]
def slots : FiniteMap String Nat := SourceStore.slotEnv ["slot"]
def base : MachineAddress := 0x1000

def frame : Provenance :=
  { space := .cpuVirtual, root := alloc, epoch := epoch, source := .stack
    rootExtent := ⟨0, 4096⟩, path := [] }

def record : AllocationRecord :=
  { extent := frame.rootExtent, epoch := epoch, space := .cpuVirtual
    source := .stack, owners := [owner], permission := .readWrite, live := true
    bytes := .empty, base := some base }

def state : MemoryState :=
  (MemoryState.empty.allocate? alloc record).getD .empty

/-- The generic local resolver is inhabited for this real frame geometry. -/
example :
    (LocalAddress.resolve? frameLayout rootOffset slots "slot" 4).isSome = true := by
  decide +kernel

/-- A resolver-produced local address reaches the address recorded by the
allocated state.  All geometry is read from `address`; the proof names no
computed local displacement. -/
theorem resolved_address_reaches_placement {address : LocalAddress.Result}
    (resolved : LocalAddress.resolve? frameLayout rootOffset slots "slot" 4 =
      some address) :
    state.addressAt? frame.root address.range.start =
      some (FrameAddressing.effectiveAddress
        (addressOf base address.rootOffset) address) := by
  have exact := LocalAddress.resolve?_exact resolved
  have layoutExact : address.layout = frameLayout := exact.1
  have rootExact : address.rootOffset = rootOffset := exact.2.1
  apply FrameAddressing.addressAt?_eq_effectiveAddress
      state address frame record base (addressOf base address.rootOffset)
  · decide
  · rfl
  · decide
  · simp [frame]
  · rfl
  · rw [layoutExact, rootExact]
    decide
  · show base.toNat + record.extent.stop ≤ 2 ^ 64
    change 4096 + 4096 ≤ 2 ^ 64
    omega
  · rfl

end Grass.Tests.Assembly.FrameAddressing
