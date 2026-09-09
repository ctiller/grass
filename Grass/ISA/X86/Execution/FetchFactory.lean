import Grass.ISA.X86.Execution.AccessPolicy
import Grass.ISA.X86.Execution.Dispatch
import Grass.ISA.X86.Execution.RunFactory

/-!
# Checked instruction-fetch factory

The lookahead in this module chooses a bounded access footprint. Only the
subsequent `RunFactory.access` receipt proves that bytes were actually read.
This is a checked normal-fetch constructor, not complete physical fault coverage.
-/

namespace Grass.ISA.X86.Execution.FetchFactory

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

private def lookahead (memory : MemoryState) (root : AllocId) (offset fuel : Nat) : ByteSeq :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      match memory.byteAt? root offset with
      | none => []
      | some byte => byte :: lookahead memory root (offset + 1) fuel

private def footprint (rip : MachineAddress) (bytes : ByteSeq) : Nat :=
  match DecodedSite.check rip bytes with
  | .ok site => site.encoding.size
  | .error _ => max 1 bytes.length

def fetchPolicy (policy : CpuAccessPolicy) : StepPolicy :=
  { policy.operationPolicy with
    oracle := Oracle.ofMemory (fun _ _ => []) (fun _ _ _ => 0) }

inductive Failure where
  | address (before : State) (reason : AddressPlanFailure)
  | access (reached : State) (descriptor : AccessDescriptor)
      (reason : RunFactory.AccessFailure descriptor)
  | applicability (reached : State) (reason : ApplicabilityFailure)

structure Success (policy : CpuAccessPolicy) (before : State) where
  after : MachineState
  observed : ObservedFetch before after
  plan : AddressPlan before.machine.memory policy.code before.rip
  descriptor_exact : observed.descriptor =
    plan.descriptor policy .fetch observed.descriptor.range.size
  dispatched : Dispatched before after
  dispatch_exact : observed.dispatch = .ok dispatched
  policy_exact : observed.run.policy = fetchPolicy policy
  context_exact : observed.run.context = policy.context
  contextKind_exact : observed.run.contextKind = policy.contextKind
  cause_exact : observed.run.cause = policy.cause
  descriptorContext : observed.descriptor.context = policy.context

private def accessReached (before : State) {descriptor : AccessDescriptor} :
    RunFactory.AccessFailure descriptor → State
  | .rejected _ => before
  | .violations after | .preparationUnavailable after _ | .answerUnavailable after =>
      { before with machine := after }

/-- Plan from actual code placement, choose at most fifteen present bytes, run
the exact execute access, and dispatch only its actual observation. -/
def fetch (policy : CpuAccessPolicy) (before : State) :
    Except Failure (Success policy before) :=
  match planned : planAddress before.machine.memory policy.code before.rip with
  | .error reason => .error (.address before reason)
  | .ok plan =>
      let preview := lookahead before.machine.memory policy.code.root plan.offset 15
      let descriptor := plan.descriptor policy .fetch (footprint before.rip preview)
      match ran : RunFactory.access (fetchPolicy policy) before.machine descriptor
          policy.context policy.contextKind policy.cause with
      | .error reason => .error (.access (accessReached before reason) descriptor reason)
      | .ok result =>
          let after := result.after
          let run := result.run
          have allocationEq : run.resolved.allocation = plan.allocation := by
            exact Option.some.inj (run.resolved.allocationLookup.symm.trans plan.lookup)
          let observed : ObservedFetch before after :=
            { descriptor := descriptor
              run := run
              writeData := fun _ _ => []
              indeterminate := fun _ _ _ => 0
              memoryOracle := by rw [result.policy_exact]; rfl
              intent := rfl
              initialization := rfl
              ledgerEffect := rfl
              authorityEffect := rfl
              address := rfl
              placed := ⟨plan.base, by rw [allocationEq]; exact plan.placed⟩ }
          match dispatched : observed.dispatch with
          | .error reason =>
              .error (.applicability { before with machine := after } reason)
          | .ok selected =>
              .ok
                { after := after
                  observed := observed
                  plan := plan
                  descriptor_exact := rfl
                  dispatched := selected
                  dispatch_exact := dispatched
                  policy_exact := result.policy_exact
                  context_exact := result.context_exact
                  contextKind_exact := result.contextKind_exact
                  cause_exact := result.cause_exact
                  descriptorContext := rfl }

end Grass.ISA.X86.Execution.FetchFactory
