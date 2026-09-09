import Grass.Disasm.Spatial

/-!
# Decoded-footprint spatial integration controls

These conditional controls combine a checked decode footprint with a live,
resolved object in one constructed state. They are not certificates about the
input binary: they do not establish file-to-bytes connection, fetch,
reachability, a raw memory transition, or a native committed write.
-/

namespace Grass.Tests.Disasm.Spatial

open Grass.Core Grass.Std.Logical Grass.Memory Grass.Memory.SpatialAccess
  Grass.Disasm Grass.Disasm.Spatial Grass.Disasm.StoreAttempt Grass.ISA.X86
  Grass.ISA.X86.Execution

private def allocs : FreshSupply AllocTag := .initial
private def backings : FreshSupply StorageTag := .initial
private def contexts : FreshSupply ContextTag := .initial

private def allocation : AllocId := allocs.fresh.1
private def backing : StorageId := backings.fresh.1
private def caller : ContextId := contexts.fresh.1
private def epoch : EpochId := (FreshSupply.initial (Tag := EpochTag)).fresh.1

/-- The root is deliberately larger than the object, so the bad store is an
object-boundary result, not an allocation-boundary result. -/
private def allocationRecord : AllocationRecord :=
  { extent := ⟨0, 16⟩, epoch := epoch, space := .cpuVirtual
    source := .virtualAlloc, owners := [caller], permission := .readWrite, live := true
    backing := backing, origin := 0, base := some 0x2000 }

private def backingRecord : BackingRecord := { capacity := 16, bytes := .empty }

private def objectStep : ProvenanceStep :=
  { kind := .object, label := ⟨"object8"⟩, extent := ⟨0, 8⟩ }

private def provenance : Provenance :=
  { space := .cpuVirtual, root := allocation, epoch := epoch
    source := .virtualAlloc, rootExtent := ⟨0, 16⟩, path := [objectStep] }

private def memory? : Option MemoryState := do
  let initial ← MemoryState.empty.installBacking? backing backingRecord
  initial.allocate? allocation allocationRecord

theorem checked_memory_setup_succeeds : memory?.isSome := by decide

/-- Setup is consumed as a proof argument, never replaced by a fallback state. -/
private def memory : MemoryState := memory?.get checked_memory_setup_succeeds

private def rip : BitVec 64 := 0x140001000

private def state : State :=
  { machine := MachineState.initial memory
    gpr := fun register => if register = .rcx then 0x2000 else 0
    rip := rip
    rflags := 0 }

private def resolvedObject :
    state.machine.memory.ResolvedAccess provenance provenance.extent :=
  (state.machine.memory.resolveAccess? provenance provenance.extent).toOption.get (by decide)

private theorem objectAllocation_eq : resolvedObject.allocation = allocationRecord := by
  apply Option.some.inj
  exact resolvedObject.allocationLookup.symm.trans (by decide)

private theorem placement_does_not_wrap :
    FitsAllocation (0x2000 : MachineAddress) allocationRecord.extent.stop := by
  change (0x2000 : MachineAddress).toNat + 16 ≤ 2 ^ 64
  have hbase : (0x2000 : MachineAddress).toNat = 8192 := by decide
  have hpow : (2 : Nat) ^ 14 ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have h14 : (16384 : Nat) = 2 ^ 14 := by decide
  omega

private def object : PlacedObject state.machine.memory provenance where
  resolved := resolvedObject
  base := 0x2000
  placed := by
    rw [objectAllocation_eq]
    rfl
  noWrap := by
    rw [objectAllocation_eq]
    exact placement_does_not_wrap

/-- The exact imported MSVC corpus instruction bytes, followed by RET. -/
private def safeBytes : ByteSeq := [0xc7, 0x41, 0x04, 0x2a, 0, 0, 0, 0xc3]
private def badBytes : ByteSeq := [0xc7, 0x41, 0x08, 0x2a, 0, 0, 0, 0xc3]

private def safeEvidence? : Option (Evidence rip safeBytes state) :=
  match check rip safeBytes state with
  | .ok evidence => some evidence
  | .error _ => none

private def badEvidence? : Option (Evidence rip badBytes state) :=
  match check rip badBytes state with
  | .ok evidence => some evidence
  | .error _ => none

theorem safe_store_check_succeeds : safeEvidence?.isSome := by decide
theorem bad_store_check_succeeds : badEvidence?.isSome := by decide

/-- Both evidence values are obtained through `StoreAttempt.check` and its
success proof, rather than manufactured with record fields. -/
private def safeEvidence : Evidence rip safeBytes state :=
  safeEvidence?.get safe_store_check_succeeds

private def badEvidence : Evidence rip badBytes state :=
  badEvidence?.get bad_store_check_succeeds

example : safeEvidence.base = .rcx ∧ safeEvidence.address = 0x2004 ∧
    safeEvidence.width = 4 ∧ safeEvidence.immediate = 42 := by decide

example : badEvidence.base = .rcx ∧ badEvidence.address = 0x2008 ∧
    badEvidence.width = 4 ∧ badEvidence.immediate = 42 := by decide

private def safeAssessment : Assessment safeEvidence object := assess safeEvidence object
private def badAssessment : Assessment badEvidence object := assess badEvidence object

private theorem safe_has_no_outside_byte :
    outsideIndex? object (footprint safeEvidence) = none := by decide

/-- The decoded `[RCX+4]` width-four candidate remains entirely in object8. -/
theorem safe_decoded_footprint_within_object :
    WithinObject object (footprint safeEvidence) :=
  (outsideIndex?_eq_none_iff object (footprint safeEvidence)).mp safe_has_no_outside_byte

/-- `assess` selects its safe branch for the exact decoded footprint. -/
def safeAssessmentIsWithin : Bool :=
  match safeAssessment with
  | .within _ => true
  | .outside _ _ => false

example : safeAssessmentIsWithin = true := by decide

private theorem bad_first_byte_is_outside :
    outsideIndex? object (footprint badEvidence) = some 0 := by decide

/-- The decoded `[RCX+8]` candidate's first byte is beyond object8 while still
inside the same 16-byte root allocation. -/
theorem bad_decoded_footprint_has_outside_byte :
    OutsideByte object (footprint badEvidence) 0 :=
  outsideIndex?_sound object (footprint badEvidence) bad_first_byte_is_outside

theorem bad_decoded_footprint_not_within_object :
    ¬ WithinObject object (footprint badEvidence) :=
  excluded_not_within badEvidence object bad_decoded_footprint_has_outside_byte

/-- `assess` selects its excluded-byte branch for the exact decoded footprint. -/
def badAssessmentIsOutside : Bool :=
  match badAssessment with
  | .within _ => false
  | .outside _ _ => true

example : badAssessmentIsOutside = true := by decide

end Grass.Tests.Disasm.Spatial
