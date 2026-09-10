import Grass.Assembly.PrologueExecution
import Grass.ISA.X86.Execution.PushFactory
import Grass.ISA.X86.Execution.ComputationFactory
import Grass.Platform.Win32.CpuPolicy

/-! Construct the source-derived prologue through the actual Windows CPU
policy and conditional normal instruction factories. Failures retain the state
reached by the attempted prefix; this is not an exhaustive execution claim. -/

namespace Grass.Assembly.PrologueFactory

open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

inductive Reason where
  | policyUnavailable
  | push (failure : PushFactory.Failure)
  | wrongPush (expected actual : Gpr)
  | allocation (failure : ComputationFactory.Failure)
  | wrongAllocation (expected actual : ImmediateArithmetic.Immediate)
  | allocationUnderflow

structure Failure where
  reached : State
  reason : Reason

private def fetchFailureReached : FetchFactory.Failure → State
  | .address before _ => before
  | .access reached _ _ => reached
  | .applicability reached _ => reached

private def pushFailureReached (_before : State) : PushFactory.Failure → State
  | .fetch failure => fetchFailureReached failure
  | .unsupported reached _ => reached
  | .stackUnderflow reached => reached
  | .stackAddress reached _ => reached
  | .store reached _ _ => reached

private def computationFailureReached (_before : State) : ComputationFactory.Failure → State
  | .fetch failure => fetchFailureReached failure
  | .unsupported reached _ => reached
  | .accessFreeRejected reached _ => reached

structure PushSuccess (registers : List Gpr) (before : State) where
  after : State
  run : PrologueExecution.PushRun registers before after

private def runPushes {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    (registers : List Gpr) → (before : State) → Except Failure (PushSuccess registers before)
  | [], before => .ok ⟨before, .nil before⟩
  | expected :: registers, before =>
      match hp : Cpu.policy? loaded before with
      | none => .error ⟨before, .policyUnavailable⟩
      | some policy =>
          match PushFactory.push policy before with
          | .error failure => .error ⟨pushFailureReached before failure, .push failure⟩
          | .ok pushed =>
              if registerExact : pushed.register = expected then
                match runPushes loaded registers pushed.receipt.result with
                | .error failure => .error failure
                | .ok rest =>
                    .ok ⟨rest.after, by
                      subst expected
                      exact .cons pushed.receipt rest.run⟩
              else .error ⟨pushed.receipt.result, .wrongPush expected pushed.register⟩

/-- Execute all source-derived saved-register pushes and then the derived stack
allocation. Every policy is recomputed from the actual current state. -/
def execute {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (prologue : SourcePrologue.Result)
    (before : State) : Except Failure
      (Sigma fun after => PrologueExecution.Result prologue before after) :=
  match runPushes loaded prologue.frame.saved.registers before with
  | .error failure => .error failure
  | .ok pushed =>
      match hp : Cpu.policy? loaded pushed.after with
      | none => .error ⟨pushed.after, .policyUnavailable⟩
      | some policy =>
          match ComputationFactory.subRsp policy pushed.after with
          | .error failure =>
              .error ⟨computationFailureReached pushed.after failure, .allocation failure⟩
          | .ok allocated =>
              if immediateExact : allocated.immediate = prologue.allocation.immediate then
                if fits : prologue.frame.layout.callAllocationBytes ≤
                    (pushed.after.gpr .rsp).toNat then
                  let allocationReceipt : SubRspNormal pushed.after allocated.afterFetch
                      allocated.afterCompute prologue.allocation.immediate :=
                    immediateExact ▸ allocated.receipt
                  .ok ⟨allocationReceipt.result, by
                    exact
                      { afterPushes := pushed.after
                        pushes := pushed.run
                        afterAllocationFetch := allocated.afterFetch
                        afterAllocationCompute := allocated.afterCompute
                        allocation := allocationReceipt
                        allocationFits := fits
                        afterExact := rfl }⟩
                else .error ⟨allocated.receipt.result, .allocationUnderflow⟩
              else
                .error ⟨allocated.receipt.result,
                  .wrongAllocation prologue.allocation.immediate allocated.immediate⟩

end Grass.Assembly.PrologueFactory
