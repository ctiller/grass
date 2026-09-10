import Grass.ISA.X86.Execution.State
import Grass.Memory.SpatialAccess

/-!
# Declared callable data-object model

This factory constructs an explicit caller contract for conditional analysis.
It is a checked model state, not an observation of native state, a code-fetch
fact, an entry/reachability proof, or an x86 transition.
-/
namespace Grass.Disasm.CallerObject

open Grass.Core Grass.Memory Grass.Memory.SpatialAccess Grass.ISA.X86
  Grass.ISA.X86.Execution Grass.Std.Logical

inductive Error where
  | objectOutsideRoot
  | placementWraps
  | backingInstallation
  | allocationInstallation
  | objectResolution (failure : MemoryState.ResolveFailure)
deriving DecidableEq, Repr

private def allocSupply : FreshSupply AllocTag := .initial
private def backingSupply : FreshSupply StorageTag := .initial
private def contextSupply : FreshSupply ContextTag := .initial
private def epochSupply : FreshSupply EpochTag := .initial

private def allocation : AllocId := allocSupply.fresh.1
private def backing : StorageId := backingSupply.fresh.1
private def caller : ContextId := contextSupply.fresh.1
private def epoch : EpochId := epochSupply.fresh.1

/-- The result of declaring one live writable object at RCX. `.virtualAlloc` is
an explicit model choice supplied by this factory, not recovered allocator
provenance. -/
structure Result (base : MachineAddress) (objectSize rootSize : Nat)
    (rip : MachineAddress) where
  state : State
  provenance : Provenance
  object : PlacedObject state.machine.memory provenance
  rcxAtStart : state.gpr .rcx = base
  ripAtEntry : state.rip = rip
  objectExtent : provenance.extent = ⟨0, objectSize⟩
  rootExtent : provenance.rootExtent = ⟨0, rootSize⟩
  objectWithinRoot : provenance.rootExtent.Contains provenance.extent
  modeledSource : provenance.source = .virtualAlloc

/-- Construct the declared object through the public checked backing,
allocation, and resolution doors. No failed branch substitutes a fallback
state. -/
def check (base : MachineAddress) (objectSize rootSize : Nat)
    (rip : MachineAddress) : Except Error (Result base objectSize rootSize rip) :=
  if hcontained : objectSize ≤ rootSize then
    if hfits : FitsAllocation base rootSize then
      let allocationRecord : AllocationRecord :=
        { extent := ⟨0, rootSize⟩, epoch := epoch, space := .cpuVirtual
          source := .virtualAlloc, owners := [caller], permission := .readWrite
          live := true, backing := backing, origin := 0, base := some base }
      let backingRecord : BackingRecord := { capacity := rootSize, bytes := .empty }
      let provenance : Provenance :=
        { space := .cpuVirtual, root := allocation, epoch := epoch
          source := .virtualAlloc, rootExtent := ⟨0, rootSize⟩
          path := [{ kind := .object, label := ⟨"declared-caller-object"⟩
                     extent := ⟨0, objectSize⟩ }] }
      match hb : MemoryState.empty.installBacking? backing backingRecord with
      | none => .error .backingInstallation
      | some withBacking =>
          match ha : withBacking.allocate? allocation allocationRecord with
          | none => .error .allocationInstallation
          | some memory =>
              match hr : memory.resolveAccess? provenance provenance.extent with
              | .error failure => .error (.objectResolution failure)
              | .ok resolved =>
                  let machine := MachineState.initial memory
                  let state : State :=
                    { machine := machine
                      gpr := fun register => if register = .rcx then base else 0
                      rip := rip
                      rflags := 0 }
                  .ok {
                    state := state
                    provenance := provenance
                    object := {
                      resolved := resolved
                      base := base
                      placed := by
                        have lookup : memory.allocations.lookup allocation =
                            some allocationRecord := MemoryState.allocate?_lookup_self ha
                        have equalRecord : resolved.allocation = allocationRecord := by
                          apply Option.some.inj
                          exact resolved.allocationLookup.symm.trans lookup
                        rw [equalRecord]
                      noWrap := by
                        have lookup : memory.allocations.lookup allocation =
                            some allocationRecord := MemoryState.allocate?_lookup_self ha
                        have equalRecord : resolved.allocation = allocationRecord := by
                          apply Option.some.inj
                          exact resolved.allocationLookup.symm.trans lookup
                        rw [equalRecord]
                        simpa [allocationRecord, ByteRange.stop] using hfits }
                    rcxAtStart := by simp [state]
                    ripAtEntry := rfl
                    objectExtent := rfl
                    rootExtent := rfl
                    objectWithinRoot := by
                      change (⟨0, rootSize⟩ : ByteRange).Contains ⟨0, objectSize⟩
                      simpa [ByteRange.Contains, ByteRange.stop] using hcontained
                    modeledSource := rfl }
    else .error .placementWraps
  else .error .objectOutsideRoot

end Grass.Disasm.CallerObject
