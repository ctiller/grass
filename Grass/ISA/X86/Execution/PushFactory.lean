import Grass.ISA.X86.Execution.FetchFactory
import Grass.ISA.X86.Execution.PushNormal
import Grass.ISA.X86.Execution.RunFactory

/-!
# Constructive fetched register PUSH execution

`push` constructs a normal receipt from the actual fetch and computed stack
access. Address, underflow and operation failures retain their reached states.
-/

namespace Grass.ISA.X86.Execution.PushFactory

open Grass.Memory Grass.Op Grass.ISA.X86

inductive Failure where
  | fetch (reason : FetchFactory.Failure)
  | unsupported (reached : State) (instruction : Instruction)
  | stackUnderflow (reached : State)
  | stackAddress (reached : State) (reason : AddressPlanFailure)
  | store (reached : State) (descriptor : AccessDescriptor)
      (reason : RunFactory.AccessFailure descriptor)

structure Success (before : State) where
  register : Gpr
  afterFetch : MachineState
  afterStore : MachineState
  receipt : PushNormal before afterFetch afterStore register

def pushFromFetched {policy : CpuAccessPolicy} (before : State)
    (fetched : FetchFactory.Success policy before) : Except Failure (Success before) :=
      let site := fetched.dispatched.fetch
      match selected : fetched.dispatched.selection.instruction with
      | .stack (.push register) =>
          if stackBound : 8 ≤ (before.gpr .rsp).toNat then
            let address := before.gpr .rsp - 8
            match planned : planAddress fetched.after.memory policy.stack address with
            | .error reason =>
                .error (.stackAddress { before with machine := fetched.after } reason)
            | .ok plan =>
                let descriptor := plan.descriptor policy .stackWrite 8
                let storePolicy : StepPolicy :=
                  { site.run.policy with
                    oracle := Oracle.ofMemory (fun _ _ => le64 (before.gpr register))
                      (fun _ _ _ => 0) }
                match storedResult : RunFactory.access storePolicy fetched.after descriptor
                    site.run.context site.run.contextKind site.run.cause with
                | .error reason =>
                    .error (.store (RunFactory.AccessFailure.reached { before with machine := fetched.after } reason)
                      descriptor reason)
                | .ok stored =>
                    have metadata := fetched.observed.dispatch_metadata fetched.dispatched
                      fetched.dispatch_exact
                    have descriptorContext : site.descriptor.context = policy.context :=
                      (congrArg AccessDescriptor.context metadata.2.2.2.2).trans
                        fetched.descriptorContext
                    have siteContext : site.run.context = policy.context :=
                      metadata.2.1.trans fetched.context_exact
                    have fetchContext : site.descriptor.context = site.run.context := by
                      exact descriptorContext.trans siteContext.symm
                    have allocationEq : stored.run.resolved.allocation = plan.allocation := by
                      exact Option.some.inj
                        (stored.run.resolved.allocationLookup.symm.trans plan.lookup)
                    let receipt : PushNormal before fetched.after stored.after register :=
                      { fetch := site
                        encoding := by
                          have exact := fetched.dispatched.selection.encoding_eq
                          rw [selected] at exact
                          exact (Option.some.inj exact).symm
                        descriptor := descriptor
                        store := stored.run
                        policy := by rw [stored.policy_exact]
                        context := stored.context_exact
                        contextKind := stored.contextKind_exact
                        cause := stored.cause_exact
                        fetchContext := fetchContext
                        storeContext := by
                          calc
                            descriptor.context = policy.context := rfl
                            _ = site.run.context := siteContext.symm
                            _ = stored.run.context := stored.context_exact.symm
                        memoryOracle := by rw [stored.policy_exact]
                        intent := rfl
                        initialization := rfl
                        ordering := rfl
                        extent := rfl
                        initialized := rfl
                        ledgerEffect := rfl
                        authorityEffect := rfl
                        stackNoUnderflow := stackBound
                        address := rfl
                        placed := ⟨plan.base, by rw [allocationEq]; exact plan.placed⟩ }
                    .ok
                      { register := register
                        afterFetch := fetched.after
                        afterStore := stored.after
                        receipt := receipt }
          else .error (.stackUnderflow { before with machine := fetched.after })
      | instruction =>
          .error (.unsupported { before with machine := fetched.after } instruction)

def push (policy : CpuAccessPolicy) (before : State) : Except Failure (Success before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched => pushFromFetched before fetched

end Grass.ISA.X86.Execution.PushFactory
