import Grass.ISA.X86.Execution.ReturnSlotRead
import Grass.ISA.X86.Execution.AccessPolicy
import Grass.ISA.X86.Execution.RunFactory

/-!
# Checked return-slot observation

`read` computes a stack descriptor from the current pre-pop cursor and fixed
policy. Slot and context mismatches stop before the read; target mismatch
retains the actual completed read state. Provider and CPU return correspondence
are separate from these memory observations.
-/

namespace Grass.ISA.X86.Execution.ReturnSlotFactory

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

def readPolicy (policy : CpuAccessPolicy) : StepPolicy :=
  { policy.operationPolicy with oracle := Oracle.ofMemory (fun _ _ => []) (fun _ _ _ => 0) }

inductive Failure where
  | address (reached : State) (reason : AddressPlanFailure)
  | wrongSlot (reached : State) (descriptor expected : AccessDescriptor)
  | wrongContext (reached : State)
  | access (reached : State) (descriptor : AccessDescriptor)
      (reason : RunFactory.AccessFailure descriptor)
  | targetMismatch (reached : State) (actual expected : BitVec 64)

private def accessReached (before : State) {descriptor : AccessDescriptor} :
    RunFactory.AccessFailure descriptor → State
  | .rejected _ => before
  | .violations after | .preparationUnavailable after _ | .answerUnavailable after =>
      { before with machine := after }

structure Success {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} (policy : CpuAccessPolicy)
    (call : CallNormal callBefore afterFetch afterTarget afterCall displacement)
    (beforeReturn : State) where
  afterRead : MachineState
  receipt : ReturnSlotRead call beforeReturn afterRead
  plan : AddressPlan beforeReturn.machine.memory policy.stack (beforeReturn.gpr .rsp)
  descriptor_exact : receipt.descriptor = plan.descriptor policy .stackRead 8
  policy_exact : receipt.run.policy = readPolicy policy
  context_exact : receipt.run.context = policy.context
  contextKind_exact : receipt.run.contextKind = policy.contextKind
  cause_exact : receipt.run.cause = policy.cause

def read {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} (policy : CpuAccessPolicy)
    (call : CallNormal callBefore afterFetch afterTarget afterCall displacement)
    (beforeReturn : State) : Except Failure (Success policy call beforeReturn) :=
  match planned : planAddress beforeReturn.machine.memory policy.stack (beforeReturn.gpr .rsp) with
  | .error reason => .error (.address beforeReturn reason)
  | .ok plan =>
      let descriptor := plan.descriptor policy .stackRead 8
      if slot : descriptor.provenance = call.storeDescriptor.provenance ∧
          descriptor.range = call.storeDescriptor.range ∧
          descriptor.address = call.storeDescriptor.address then
        if continuity : policy.context = call.storeRun.context ∧
            policy.contextKind = call.storeRun.contextKind then
          match ran : RunFactory.access (readPolicy policy) beforeReturn.machine descriptor
              policy.context policy.contextKind policy.cause with
          | .error reason => .error (.access (accessReached beforeReturn reason) descriptor reason)
          | .ok result =>
            let read64 : ReadValue64 result.run :=
              { writeData := fun _ _ => [], indeterminate := fun _ _ _ => 0
                memoryOracle := by rw [result.policy_exact]; rfl
                reads := rfl, writes := rfl, width := rfl, initialization := rfl }
            if target : read64.value = call.fetch.site.fallthroughRip then
              .ok { afterRead := result.after
                    receipt :=
                      { descriptor := descriptor, run := result.run, read := read64
                        slotProvenance := slot.1, slotRange := slot.2.1
                        slotAddress := slot.2.2
                        context := result.context_exact.trans continuity.1
                        contextKind := result.contextKind_exact.trans continuity.2
                        descriptorContext :=
                          (show descriptor.context = policy.context from rfl).trans
                            result.context_exact.symm
                        intent := rfl, space := rfl, ordering := rfl
                        ledgerEffect := rfl, authorityEffect := rfl, address := rfl
                        placed := ⟨plan.base, by
                          have allocationEq : result.run.resolved.allocation = plan.allocation :=
                            Option.some.inj (result.run.resolved.allocationLookup.symm.trans plan.lookup)
                          rw [allocationEq]; exact plan.placed⟩, targetMatches := target }
                    plan := plan, descriptor_exact := rfl
                    policy_exact := result.policy_exact
                    context_exact := result.context_exact
                    contextKind_exact := result.contextKind_exact
                    cause_exact := result.cause_exact }
            else .error (.targetMismatch { beforeReturn with machine := result.after }
              read64.value call.fetch.site.fallthroughRip)
        else .error (.wrongContext beforeReturn)
      else .error (.wrongSlot beforeReturn descriptor call.storeDescriptor)

end Grass.ISA.X86.Execution.ReturnSlotFactory
