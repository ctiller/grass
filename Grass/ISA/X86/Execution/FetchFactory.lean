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

private theorem lookahead_prefix (memory : MemoryState) (root : AllocId)
    (offset fuel : Nat) (bytes : ByteSeq) (fits : bytes.length ≤ fuel)
    (present : ∀ i (bound : i < bytes.length),
      memory.byteAt? root (offset + i) = some bytes[i]) :
    ∃ suffix, lookahead memory root offset fuel = bytes ++ suffix := by
  induction bytes generalizing offset fuel with
  | nil => exact ⟨lookahead memory root offset fuel, rfl⟩
  | cons byte bytes ih =>
      cases fuel with
      | zero => simp at fits
      | succ fuel =>
          have head := present 0 (by simp)
          simp only [List.getElem_cons_zero] at head
          have tailPresent : ∀ i (bound : i < bytes.length),
              memory.byteAt? root ((offset + 1) + i) =
                some bytes[i] := by
            intro i bound
            have next := present (i + 1) (by simpa using Nat.succ_lt_succ bound)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
          obtain ⟨suffix, tail⟩ := ih (offset + 1) fuel (by simpa using fits) tailPresent
          refine ⟨suffix, ?_⟩
          have head' : memory.byteAt? root offset = some byte := by simpa using head
          simp [lookahead, head', tail]

private theorem footprint_eq_encoding_size (rip : MachineAddress) (encoding : InsnEncoding)
    (suffix : ByteSeq)
    (decoded : decodeInsn (encoding.toBytes ++ suffix) = .ok (encoding, suffix))
    (lengthBound : 0 < encoding.size ∧ encoding.size ≤ 15)
    (fallthroughFits : rip.toNat + encoding.size < 2 ^ 64) :
    footprint rip (encoding.toBytes ++ suffix) = encoding.size := by
  unfold footprint
  cases checked : DecodedSite.check rip (encoding.toBytes ++ suffix) with
  | error error =>
      unfold DecodedSite.check at checked
      split at checked
      · rename_i decodeError decodeEquation
        rw [decoded] at decodeEquation
        contradiction
      · rename_i output decodeEquation
        have sameOutput := Except.ok.inj (decodeEquation.symm.trans decoded)
        cases sameOutput
        simp [lengthBound, fallthroughFits] at checked
  | ok site =>
      have same : site.encoding = encoding := by
        have outputs := site.decoded.symm.trans decoded
        exact congrArg Prod.fst (Except.ok.inj outputs)
      simp [same]

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
  extent_exact : observed.descriptor.range.size = footprint before.rip
    (lookahead before.machine.memory policy.code.root plan.offset 15)
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
                  extent_exact := rfl
                  dispatched := selected
                  dispatch_exact := dispatched
                  policy_exact := result.policy_exact
                  context_exact := result.context_exact
                  contextKind_exact := result.contextKind_exact
                  cause_exact := result.cause_exact
                  descriptorContext := rfl }

/-- `Success.extent_of_memory_prefix` uses a production decoder prefix at the planned code coordinates to fix
the successful fetch descriptor to that instruction's exact encoded size. -/
theorem Success.extent_of_memory_prefix {policy : CpuAccessPolicy} {before : State}
    (success : Success policy before) (encoding : InsnEncoding)
    (lengthBound : 0 < encoding.size ∧ encoding.size ≤ 15)
    (fallthroughFits : before.rip.toNat + encoding.size < 2 ^ 64)
    (present : ∀ i (bound : i < encoding.toBytes.length),
      before.machine.memory.byteAt? policy.code.root (success.plan.offset + i) =
        some encoding.toBytes[i])
    (decodes : ∀ suffix, decodeInsn (encoding.toBytes ++ suffix) = .ok (encoding, suffix)) :
    success.observed.descriptor.range.size = encoding.size := by
  obtain ⟨suffix, preview⟩ := lookahead_prefix before.machine.memory policy.code.root
    success.plan.offset 15 encoding.toBytes (by simpa using lengthBound.2) present
  rw [success.extent_exact, preview]
  exact footprint_eq_encoding_size before.rip encoding suffix (decodes suffix)
    lengthBound fallthroughFits

end Grass.ISA.X86.Execution.FetchFactory
