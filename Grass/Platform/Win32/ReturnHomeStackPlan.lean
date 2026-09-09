import Grass.Platform.Win32.ReturnHome
import Grass.ISA.X86.EndianBridge
import Grass.ISA.X86.Execution.CallNormal
import Grass.ISA.X86.Execution.AccessPolicy

/-!
# Deterministic returning-call stack-plan construction

This checker derives the return and home slots from an actual CALL result and
the fixed stack provenance. Failures are applicability diagnostics, not CPU
faults or provider outcomes.
-/

namespace Grass.Platform.Win32.ReturnHome.StackPlanFactory

open Grass.ABI Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution

inductive Failure where
  | wrongStackProvenance
  | wrongAddressSpace
  | addressOverflow
  | returnAddress (reason : AddressPlanFailure)
  | homeAddress (reason : AddressPlanFailure)
  | returnResolution (reason : MemoryState.ResolveFailure)
  | homeResolution (reason : MemoryState.ResolveFailure)
  | allocationWrap
  | nonStackAllocation
  | returnBytes
  | returnSlotMismatch
  | overlappingSlots
deriving Repr

/-- Derive the complete two-slot ABI plan from the actual post-CALL machine.
No slot, offset, resolved access, or continuation is supplied by the caller. -/
def derive? {callBefore : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32} (policy : CpuAccessPolicy)
    (call : CallNormal callBefore afterFetch afterRead afterStore displacement) :
    Except Failure (ReturnHome.Plan call.result) :=
  if stackExact : call.storeDescriptor.provenance = policy.stack then
  if stackCPU : policy.stack.space = .cpuVirtual then
    let entryRsp := call.result.gpr .rsp
    if totalBound : entryRsp.toNat + ReturnHome.returnAddressBytes +
        ReturnHome.homeSpaceBytes ≤ 2 ^ 64 then
      match returnPlanned : planAddress call.result.machine.memory policy.stack entryRsp with
      | .error reason => .error (.returnAddress reason)
      | .ok returnPlan =>
        let returnSlot : CallMemory.Argument :=
          ⟨policy.stack, ⟨returnPlan.offset, ReturnHome.returnAddressBytes⟩⟩
        match returnResolvedExact : call.result.machine.memory.resolveAccess?
            returnSlot.provenance returnSlot.range with
        | .error reason => .error (.returnResolution reason)
        | .ok returnAccess =>
          if returnFits : FitsAllocation returnPlan.base returnAccess.allocation.extent.stop then
          if returnStack : returnAccess.allocation.source = .stack then
            let homeAddress := entryRsp + BitVec.ofNat 64 ReturnHome.returnAddressBytes
            match homePlanned : planAddress call.result.machine.memory policy.stack homeAddress with
            | .error reason => .error (.homeAddress reason)
            | .ok homePlan =>
              let homeSlot : CallMemory.Argument :=
                ⟨policy.stack, ⟨homePlan.offset, ReturnHome.homeSpaceBytes⟩⟩
              match homeResolvedExact : call.result.machine.memory.resolveAccess?
                  homeSlot.provenance homeSlot.range with
              | .error reason => .error (.homeResolution reason)
              | .ok homeAccess =>
                if homeFits : FitsAllocation homePlan.base homeAccess.allocation.extent.stop then
                  have returnAllocation : returnAccess.allocation = returnPlan.allocation :=
                    Option.some.inj (returnAccess.allocationLookup.symm.trans returnPlan.lookup)
                  have homeAllocation : homeAccess.allocation = homePlan.allocation :=
                    Option.some.inj (homeAccess.allocationLookup.symm.trans homePlan.lookup)
                  let returnResolved : CallMemory.Resolved call.result.machine.memory returnSlot :=
                    { toResolvedAccess := returnAccess
                      base := returnPlan.base
                      placed := returnAllocation ▸ returnPlan.placed
                      noWrap := returnAllocation ▸ returnFits }
                  let homeResolved : CallMemory.Resolved call.result.machine.memory homeSlot :=
                    { toResolvedAccess := homeAccess
                      base := homePlan.base
                      placed := homeAllocation ▸ homePlan.placed
                      noWrap := homeAllocation ▸ homeFits }
                  let bytes := Grass.Grammar.bitVecToLittleEndian call.fetch.site.fallthroughRip
                  if initialized : ∀ i : Fin 8,
                      returnResolved.toResolvedAccess.cellAt? (returnSlot.range.start + i.val) =
                        some (bytes.1[i.val], true) then
                    if slotExact : returnSlot.provenance = call.storeDescriptor.provenance ∧
                        returnSlot.range = call.storeDescriptor.range then
                      if separated : homeResolved.physical.Disjoint returnResolved.physical then
                        .ok
                        { continuation := call.fetch.site.fallthroughRip
                          returnSlot := returnSlot
                          returnResolved := returnResolved
                          returnCPU := stackCPU
                          returnStack := returnAllocation ▸ returnStack
                          returnSize := rfl
                          returnAddress := by
                            exact congrArg BitVec.toNat returnPlan.address_exact
                          returnObserved :=
                            { bytes := bytes, initialized := initialized
                              continuationMatches :=
                                Grass.Grammar.littleEndianToBitVec_bitVecToLittleEndian _ }
                          homeSlot := homeSlot
                          homeResolved := homeResolved
                          homeCPU := stackCPU
                          homeRoot := rfl
                          homeSize := rfl
                          homeAddress := by
                            have noWrap : entryRsp.toNat + ReturnHome.returnAddressBytes <
                                2 ^ 64 := by
                              have positive : 0 < ReturnHome.homeSpaceBytes := by decide
                              omega
                            have numeric : homeAddress.toNat =
                                entryRsp.toNat + ReturnHome.returnAddressBytes := by
                              simp only [homeAddress, BitVec.toNat_add, BitVec.toNat_ofNat]
                              rw [Nat.mod_eq_of_lt (by decide : ReturnHome.returnAddressBytes < 2 ^ 64)]
                              exact Nat.mod_eq_of_lt noWrap
                            rw [← numeric]
                            exact congrArg BitVec.toNat homePlan.address_exact
                          homeReturnSeparated := separated }
                      else .error .overlappingSlots
                    else .error .returnSlotMismatch
                  else .error .returnBytes
                else .error .allocationWrap
          else .error .nonStackAllocation
          else .error .allocationWrap
    else .error .addressOverflow
  else .error .wrongAddressSpace
  else .error .wrongStackProvenance

theorem continuation_exact {callBefore : State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32} {policy : CpuAccessPolicy}
    {call : CallNormal callBefore afterFetch afterRead afterStore displacement}
    {plan : ReturnHome.Plan call.result}
    (success : derive? policy call = .ok plan) :
    plan.continuation = call.fetch.site.fallthroughRip := by
  unfold derive? at success
  grind

theorem return_provenance_exact {callBefore : State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {policy : CpuAccessPolicy}
    {call : CallNormal callBefore afterFetch afterRead afterStore displacement}
    {plan : ReturnHome.Plan call.result}
    (success : derive? policy call = .ok plan) :
    plan.returnSlot.provenance = call.storeDescriptor.provenance := by
  unfold derive? at success
  grind

theorem return_range_exact {callBefore : State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {policy : CpuAccessPolicy}
    {call : CallNormal callBefore afterFetch afterRead afterStore displacement}
    {plan : ReturnHome.Plan call.result}
    (success : derive? policy call = .ok plan) :
    plan.returnSlot.range = call.storeDescriptor.range := by
  unfold derive? at success
  grind

end Grass.Platform.Win32.ReturnHome.StackPlanFactory

