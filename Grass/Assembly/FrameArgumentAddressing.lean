import Grass.Assembly.FrameArgument
import Grass.Memory.Addressing
import Grass.Memory.State

/-!
# Physical addresses for frame argument operands

`FrameArgument.Result` proves source-derived argument geometry and the exact
signed 32-bit displacement emitted for one Win64 stack-passed pointer argument.
This module connects that geometry to an actually placed, live allocation.
It stops at address correspondence: instruction execution, an attempted write,
permission, and the bytes written remain separate target obligations.
-/

namespace Grass.Assembly.FrameArgumentAddressing

open Grass.ISA.X86 Grass.Memory

/-- The x86-64 effective address denoted by the emitted stack-argument
displacement, when `rsp` has its post-prologue value. -/
def effectiveAddress (rsp : MachineAddress) (result : FrameArgument.Result) :
    MachineAddress :=
  rsp + BitVec.signExtend 64 (BitVec.ofNat 32 result.displacement)

private theorem signExtend_displacement (result : FrameArgument.Result) :
    BitVec.signExtend 64 (BitVec.ofNat 32 result.displacement) =
      BitVec.ofNat 64 result.displacement := by
  unfold BitVec.signExtend
  rw [result.signed_displacement]
  rfl

/-- The source-admitted immediate has exactly the qword register value that the
`mov r/m64, imm32` encoding denotes. This is a bit-vector fact only: it does
not claim that an instruction wrote any bytes. -/
theorem signExtend_immediate (result : FrameArgument.Result) :
    BitVec.signExtend 64 (BitVec.ofNat 32 result.value) =
      BitVec.ofNat 64 result.value := by
  unfold BitVec.signExtend
  rw [result.signed_immediate]
  rfl

/--
The bounded physical-address bridge for one source-derived stack argument.

The allocation lookup, placement, liveness, and extent agreement are separate
hypotheses because none implies the others in the memory model. `frameContains`
links the result's source-derived frame interval to the live provenance; then
`result.frame_contains` supplies the exact eight-byte argument range. `fits`
excludes 64-bit wrap for every object byte.
-/
theorem address_correspondence
    (state : MemoryState) (result : FrameArgument.Result)
    (frame : Provenance) (record : AllocationRecord) (base rsp : MachineAddress)
    (_found : state.allocations.lookup frame.root = some record)
    (_placed : record.base = some base)
    (_live : state.Live frame)
    (nested : frame.Nested)
    (extentExact : record.extent = frame.rootExtent)
    (frameContains : frame.extent.Contains
      (result.frame.layout.frameRange.shift result.rootOffset))
    (fits : FitsAllocation base record.extent.stop)
    (rspExact : rsp = addressOf base result.rootOffset) :
    effectiveAddress rsp result = addressOf base result.range.start ∧
      (effectiveAddress rsp result).toNat = base.toNat + result.range.start ∧
      ∀ i, i < result.range.size →
        effectiveAddress rsp result + BitVec.ofNat 64 i =
          addressOf base (result.range.start + i) ∧
        (addressOf base (result.range.start + i)).toNat =
          base.toNat + result.range.start + i := by
  have rootContains : record.extent.Contains result.range := by
    rw [extentExact]
    exact (Provenance.extent_within_root nested).trans
      (frameContains.trans result.frame_contains)
  have rangeBound : result.range.WithinBound record.extent.stop :=
    (show record.extent.WithinBound record.extent.stop from Nat.le_refl _).of_contains
      rootContains
  have startBound : result.range.start < record.extent.stop := by
    rw [ByteRange.withinBound_def] at rangeBound
    have positive : 0 < result.range.size := by
      change 0 < 8
      omega
    omega
  have effectiveEq : effectiveAddress rsp result =
      addressOf base result.range.start := by
    rw [rspExact]
    unfold effectiveAddress addressOf FrameArgument.Result.range
    rw [signExtend_displacement]
    rw [BitVec.ofNat_add]
    exact BitVec.add_assoc _ _ _
  refine ⟨effectiveEq, ?_, ?_⟩
  · rw [effectiveEq]
    exact toNat_addressOf fits startBound
  · intro i hi
    have byteBound : result.range.start + i < record.extent.stop := by
      rw [ByteRange.withinBound_def] at rangeBound
      omega
    constructor
    · rw [effectiveEq]
      simp only [addressOf, BitVec.ofNat_add]
      exact BitVec.add_assoc _ _ _
    · rw [toNat_addressOf fits byteBound]
      omega

/-- The same bridge through the allocation lookup used by `MemoryState`. The
result is conditional on explicit lookup, placement, liveness, provenance, and
nonwrapping witnesses; it does not establish instruction execution. -/
theorem addressAt?_eq_effectiveAddress
    (state : MemoryState) (result : FrameArgument.Result)
    (frame : Provenance) (record : AllocationRecord) (base rsp : MachineAddress)
    (found : state.allocations.lookup frame.root = some record)
    (placed : record.base = some base)
    (live : state.Live frame)
    (nested : frame.Nested)
    (extentExact : record.extent = frame.rootExtent)
    (frameContains : frame.extent.Contains
      (result.frame.layout.frameRange.shift result.rootOffset))
    (fits : FitsAllocation base record.extent.stop)
    (rspExact : rsp = addressOf base result.rootOffset) :
    state.addressAt? frame.root result.range.start =
      some (effectiveAddress rsp result) := by
  have physical := (address_correspondence state result frame record base rsp
    found placed live nested extentExact frameContains fits rspExact).1
  unfold MemoryState.addressAt?
  rw [found]
  simp only [Option.bind_some, placed, Option.map_some, Option.some.injEq]
  exact physical.symm

end Grass.Assembly.FrameArgumentAddressing
