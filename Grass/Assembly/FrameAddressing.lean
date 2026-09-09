import Grass.Assembly.LocalAddress
import Grass.Memory.Addressing
import Grass.Memory.State

/-!
# Physical addresses for frame-local operands

`LocalAddress.Result` proves allocation-relative frame geometry.  This module
bridges that geometry to the machine address of an actually placed, live stack
allocation.  It deliberately stops at address correspondence: instruction
execution and the value loaded or stored remain ISA-profile obligations.

The result uses the memory model's fixed 64-bit `MachineAddress`.  It does not
establish segment-base interpretation, CPU-stack provenance identity, x86-64
canonicality, access authorization, or instruction execution.  A downstream
profile must supply those target-specific facts.
-/

namespace Grass.Assembly.FrameAddressing

open Grass.ISA.X86 Grass.Memory

/-- The x86-64 effective address denoted by the displacement emitted for a
local address, when `rsp` has its post-prologue value. -/
def effectiveAddress (rsp : MachineAddress) (address : LocalAddress.Result) :
    MachineAddress :=
  rsp + BitVec.signExtend 64 (BitVec.ofNat 32 address.displacement)

private theorem signExtend_displacement (address : LocalAddress.Result) :
    BitVec.signExtend 64 (BitVec.ofNat 32 address.displacement) =
      BitVec.ofNat 64 address.displacement := by
  unfold BitVec.signExtend
  rw [address.signed_displacement]
  rfl

/--
The bounded physical-address bridge for a frame-local operand.

The allocation lookup, placement, liveness, and extent agreement are separate
hypotheses because none implies the others in the memory model.  `frameContains`
connects the computed frame to the live frame provenance, while `fits` rules out
64-bit wrap for the allocation's reachable offsets.
-/
theorem address_correspondence
    (state : MemoryState) (address : LocalAddress.Result)
    (frame : Provenance) (record : AllocationRecord) (base rsp : MachineAddress)
    (_found : state.allocations.lookup frame.root = some record)
    (_placed : record.base = some base)
    (_live : state.Live frame)
    (nested : frame.Nested)
    (extentExact : record.extent = frame.rootExtent)
    (frameContains : frame.extent.Contains
      (address.layout.frameRange.shift address.rootOffset))
    (fits : FitsAllocation base record.extent.stop)
    (rspExact : rsp = addressOf base address.rootOffset) :
    effectiveAddress rsp address = addressOf base address.range.start ∧
      (effectiveAddress rsp address).toNat = base.toNat + address.range.start ∧
      ∀ i, i < address.width →
        effectiveAddress rsp address + BitVec.ofNat 64 i =
          addressOf base (address.range.start + i) ∧
        (addressOf base (address.range.start + i)).toNat =
          base.toNat + address.range.start + i := by
  have rootContains : record.extent.Contains address.range := by
    rw [extentExact]
    exact (Provenance.extent_within_root nested).trans
      (frameContains.trans address.range_in_frame)
  have rangeBound : address.range.WithinBound record.extent.stop :=
    (show record.extent.WithinBound record.extent.stop from Nat.le_refl _).of_contains
      rootContains
  have startBound : address.range.start < record.extent.stop := by
    rw [ByteRange.withinBound_def] at rangeBound
    have positive := address.positiveWidth
    change address.range.start + address.width ≤ record.extent.stop at rangeBound
    omega
  have effectiveEq : effectiveAddress rsp address =
      addressOf base address.range.start := by
    rw [rspExact]
    unfold effectiveAddress addressOf LocalAddress.Result.range
    rw [signExtend_displacement]
    rw [BitVec.ofNat_add]
    exact BitVec.add_assoc _ _ _
  refine ⟨effectiveEq, ?_, ?_⟩
  · rw [effectiveEq]
    exact toNat_addressOf fits startBound
  · intro i hi
    have byteBound : address.range.start + i < record.extent.stop := by
      rw [ByteRange.withinBound_def] at rangeBound
      change address.range.start + address.width ≤ record.extent.stop at rangeBound
      omega
    constructor
    · rw [effectiveEq]
      simp only [addressOf, BitVec.ofNat_add]
      exact BitVec.add_assoc _ _ _
    · rw [toNat_addressOf fits byteBound]
      omega

/-- The same bridge through the lookup operation used by the memory state.  The
result is non-vacuous because lookup and placement are explicit witnesses. -/
theorem addressAt?_eq_effectiveAddress
    (state : MemoryState) (address : LocalAddress.Result)
    (frame : Provenance) (record : AllocationRecord) (base rsp : MachineAddress)
    (found : state.allocations.lookup frame.root = some record)
    (placed : record.base = some base)
    (live : state.Live frame)
    (nested : frame.Nested)
    (extentExact : record.extent = frame.rootExtent)
    (frameContains : frame.extent.Contains
      (address.layout.frameRange.shift address.rootOffset))
    (fits : FitsAllocation base record.extent.stop)
    (rspExact : rsp = addressOf base address.rootOffset) :
    state.addressAt? frame.root address.range.start =
      some (effectiveAddress rsp address) := by
  have physical := (address_correspondence state address frame record base rsp
    found placed live nested extentExact frameContains fits rspExact).1
  unfold MemoryState.addressAt?
  rw [found]
  simp only [Option.bind_some, placed, Option.map_some, Option.some.injEq]
  exact physical.symm

end Grass.Assembly.FrameAddressing
