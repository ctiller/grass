import Grass.ISA.X86.Execution.State
import Grass.Op.Step

/-!
# Fixed inputs and address planning for the CPU factory

The policy names code and stack provenance, a data-span provenance selector,
the execution context, and the admitted generic operation policy. `planAddress` obtains the allocation
and base from the current memory state. `AddressPlan.descriptor` computes the
descriptor from that placement and the requested physical address and width;
the caller does not supply an independent range or operation.

This leaf does not execute an access or prove the physical completeness of a
fault list. Profile/source correspondence and later rejected or faulted outcomes
remain separate obligations.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

inductive AccessPurpose where
  | fetch
  | dataRead
  | stackRead
  | stackWrite
deriving DecidableEq, Repr

/-- Fixed profile inputs for instruction fetches and stack/data accesses. -/
structure CpuAccessPolicy where
  operationPolicy : StepPolicy
  context : ContextId
  contextKind : ContextKind
  cause : EventCause
  code : Provenance
  stack : Provenance
  /-- The fixed platform resolves a readable data span; absence is an applicability gap. -/
  data : MachineAddress → Nat → Option Provenance := fun _ _ => none
  /-- The target's declared access-fault vocabulary; declaration is not fault exclusion. -/
  faults : AccessPurpose → List FaultClassId

inductive AddressPlanFailure where
  | missingAllocation
  | unplacedAllocation
  | addressBeforeAllocation
deriving DecidableEq, Repr

/-- `lookup`, `placed` and `notBefore` certify the placement used to compute a range. -/
structure AddressPlan (memory : MemoryState) (provenance : Provenance)
    (address : MachineAddress) where
  allocation : AllocationRecord
  base : MachineAddress
  lookup : memory.allocations.lookup provenance.root = some allocation
  placed : allocation.base = some base
  notBefore : base.toNat ≤ address.toNat

/-- `planAddress` rejects absent placement and negative allocation-local offsets. -/
def planAddress (memory : MemoryState) (provenance : Provenance) (address : MachineAddress) :
    Except AddressPlanFailure (AddressPlan memory provenance address) :=
  match lookup : memory.allocations.lookup provenance.root with
  | none => .error .missingAllocation
  | some allocation =>
      match placed : allocation.base with
      | none => .error .unplacedAllocation
      | some base =>
          if notBefore : base.toNat ≤ address.toNat then
            .ok ⟨allocation, base, lookup, placed, notBefore⟩
          else .error .addressBeforeAllocation

namespace AddressPlan

/-- The allocation-local offset determined by the observed base and numeric address. -/
def offset {memory : MemoryState} {provenance : Provenance} {address : MachineAddress}
    (plan : AddressPlan memory provenance address) : Nat := address.toNat - plan.base.toNat

/-- `descriptor` fixes CPU space, plain ordering, initialization, context and neutral ghost effects. -/
def descriptor {memory : MemoryState} {provenance : Provenance} {address : MachineAddress}
    (plan : AddressPlan memory provenance address) (policy : CpuAccessPolicy)
    (purpose : AccessPurpose) (width : Nat) : AccessDescriptor :=
  { context := policy.context
    address := .numeric address
    space := .cpuVirtual
    provenance := provenance
    range := ⟨plan.offset, width⟩
    intent := match purpose with
      | .fetch => .execute | .dataRead | .stackRead => .read | .stackWrite => .write
    requiredPermission := match purpose with
      | .fetch => .readExecute | .dataRead | .stackRead => .readOnly | .stackWrite => .readWrite
    alignment := 1
    initialization := match purpose with
      | .fetch | .dataRead | .stackRead => .allBytesInitialized | .stackWrite => .readsNothing
    producesInitialized := match purpose with | .stackWrite => true | _ => false
    ordering := .plain
    admittedFaults := policy.faults purpose
    restartability := .restartable
    ledgerEffect := []
    authorityEffect := [] }

theorem address_exact {memory : MemoryState} {provenance : Provenance} {address : MachineAddress}
    (plan : AddressPlan memory provenance address) : addressOf plan.base plan.offset = address := by
  apply BitVec.eq_of_toNat_eq
  simp [addressOf, offset, BitVec.toNat_add, Nat.add_sub_of_le plan.notBefore]
  exact address.isLt

end AddressPlan
end Grass.ISA.X86.Execution
