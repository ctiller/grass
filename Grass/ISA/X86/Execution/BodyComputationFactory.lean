import Grass.ISA.X86.Execution.ArithmeticNormal
import Grass.ISA.X86.Execution.BranchNormal
import Grass.ISA.X86.Execution.FetchFactory
import Grass.ISA.X86.Execution.LeaNormal
import Grass.ISA.X86.Execution.RunFactory

/-!
# Constructive arithmetic, branch and LEA execution

Each helper consumes the actual checked fetch and runs the fixed access-free
operation before constructing its normal receipt. The public wrappers obtain
that fetch themselves. Arithmetic status choices must satisfy the production
partial-flags relation; a rejected choice does not describe a physical fault.
-/

namespace Grass.ISA.X86.Execution.BodyComputationFactory

open Grass.Memory Grass.Op

inductive Failure where
  | fetch (reason : FetchFactory.Failure)
  | unsupported (reached : State) (instruction : Instruction)
  | accessFreeRejected (reached : State) (reason : StepRejection)
  | flagsRejected (reached : State) (instruction : ArithmeticInstruction)
  | targetOutOfRange (reached : State) (instruction : BranchInstruction)

private def execution {policy : CpuAccessPolicy} {before : State}
    (fetched : FetchFactory.Success policy before) {after : MachineState}
    (ran : step fetched.dispatched.fetch.run.policy fetched.after
      RunFactory.accessFreeOperation fetched.dispatched.fetch.run.context
      fetched.dispatched.fetch.run.contextKind fetched.dispatched.fetch.run.cause
      RunFactory.noFaultPlan = .ran after) : AccessFree before fetched.after after :=
  { fetch := fetched.dispatched.fetch
    operation := RunFactory.accessFreeOperation
    sequence := .none_
    selected := rfl
    noDataSubsteps := rfl
    faultAt := RunFactory.noFaultPlan
    noFault := rfl
    ran := ran }

structure ArithmeticSuccess (policy : CpuAccessPolicy) (before : State) where
  fetched : FetchFactory.Success policy before
  instruction : ArithmeticInstruction
  flags : RegisterSemantics.Flags Bool
  afterCompute : MachineState
  receipt : ArithmeticNormal before fetched.after afterCompute instruction
  fetch_exact : receipt.execution.fetch = fetched.dispatched.fetch
  status_exact : receipt.result.statusFlags = flags

namespace ArithmeticSuccess
def result {policy : CpuAccessPolicy} {before : State}
    (success : ArithmeticSuccess policy before) : State := success.receipt.result
end ArithmeticSuccess

def arithmeticFromFetched {policy : CpuAccessPolicy} (before : State)
    (flags : RegisterSemantics.Flags Bool) (fetched : FetchFactory.Success policy before) :
    Except Failure (ArithmeticSuccess policy before) :=
  let site := fetched.dispatched.fetch
  match selected : fetched.dispatched.selection.instruction with
  | .arithmetic instruction =>
      if allowed : (instruction.effect before).flags.Allows flags then
        match RunFactory.accessFree site.run.policy fetched.after site.run.context
            site.run.contextKind site.run.cause with
        | .error reason =>
            .error (.accessFreeRejected { before with machine := fetched.after } reason)
        | .ok computed =>
            let afterRflags := (before.withStatusFlags flags).rflags &&& ~~~resumeMask
            let receipt : ArithmeticNormal before fetched.after computed.1 instruction :=
              { execution := execution fetched computed.2.ran
                encoding := by
                  have exact := fetched.dispatched.selection.encoding_eq
                  rw [selected] at exact
                  exact (Option.some.inj exact).symm
                afterRflags := afterRflags
                flagsAllowed := by
                  dsimp [afterRflags]
                  rw [statusFlags_clearResume]
                  change (instruction.effect before).flags.Allows
                    (before.withStatusFlags flags).statusFlags
                  rw [State.withStatusFlags_statusFlags]
                  exact allowed
                outsideStatusFrame := by
                  have flagsMasked : flags.bits &&& ~~~statusMask = 0 := by
                    rcases flags with ⟨cf, pf, af, zf, sf, of⟩
                    cases cf <;> cases pf <;> cases af <;> cases zf <;>
                      cases sf <;> cases of <;> decide
                  dsimp [afterRflags, State.withStatusFlags]
                  calc
                    (((before.rflags &&& ~~~statusMask) ||| flags.bits) &&&
                        ~~~resumeMask) &&& ~~~statusMask =
                        (((before.rflags &&& ~~~statusMask) ||| flags.bits) &&&
                          ~~~statusMask) &&& ~~~resumeMask := by
                            ac_rfl
                    _ = (((before.rflags &&& ~~~statusMask) &&& ~~~statusMask) |||
                          (flags.bits &&& ~~~statusMask)) &&& ~~~resumeMask := by
                            rw [BitVec.and_or_distrib_right]
                    _ = (before.rflags &&& ~~~statusMask) &&& ~~~resumeMask := by
                            rw [flagsMasked]
                            simp [BitVec.and_assoc]
                resumeCleared := by simp [afterRflags, resumeMask] }
            .ok
              { fetched := fetched
                instruction := instruction
                flags := flags
                afterCompute := computed.1
                receipt := receipt
                fetch_exact := rfl
                status_exact := by
                  change RegisterSemantics.Flags.fromBits afterRflags = flags
                  dsimp [afterRflags]
                  rw [statusFlags_clearResume]
                  exact before.withStatusFlags_statusFlags flags }
      else .error (.flagsRejected { before with machine := fetched.after } instruction)
  | instruction => .error (.unsupported { before with machine := fetched.after } instruction)

def arithmetic (policy : CpuAccessPolicy) (before : State)
    (flags : RegisterSemantics.Flags Bool) :
    Except Failure (ArithmeticSuccess policy before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched => arithmeticFromFetched before flags fetched

structure BranchSuccess (policy : CpuAccessPolicy) (before : State) where
  fetched : FetchFactory.Success policy before
  instruction : BranchInstruction
  afterCompute : MachineState
  receipt : BranchNormal before fetched.after afterCompute instruction
  fetch_exact : receipt.execution.fetch = fetched.dispatched.fetch

namespace BranchSuccess
def result {policy : CpuAccessPolicy} {before : State}
    (success : BranchSuccess policy before) : State := success.receipt.result
end BranchSuccess

def branchFromFetched {policy : CpuAccessPolicy} (before : State)
    (fetched : FetchFactory.Success policy before) :
    Except Failure (BranchSuccess policy before) :=
  let site := fetched.dispatched.fetch
  match selected : fetched.dispatched.selection.instruction with
  | .branch instruction =>
      let target := Int.ofNat site.site.fallthroughRip.toNat + instruction.displacement.toInt
      if targetFits : instruction.taken before.statusFlags = true →
          0 ≤ target ∧ target < Int.ofNat (2 ^ 64) then
        match RunFactory.accessFree site.run.policy fetched.after site.run.context
            site.run.contextKind site.run.cause with
        | .error reason =>
            .error (.accessFreeRejected { before with machine := fetched.after } reason)
        | .ok computed =>
            let receipt : BranchNormal before fetched.after computed.1 instruction :=
              { execution := execution fetched computed.2.ran
                encoding := by
                  have exact := fetched.dispatched.selection.encoding_eq
                  rw [selected] at exact
                  exact (Option.some.inj exact).symm
                targetFits := targetFits }
            .ok
              { fetched := fetched
                instruction := instruction
                afterCompute := computed.1
                receipt := receipt
                fetch_exact := rfl }
      else .error (.targetOutOfRange { before with machine := fetched.after } instruction)
  | instruction => .error (.unsupported { before with machine := fetched.after } instruction)

def branch (policy : CpuAccessPolicy) (before : State) :
    Except Failure (BranchSuccess policy before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched => branchFromFetched before fetched

structure LeaSuccess (policy : CpuAccessPolicy) (before : State) where
  fetched : FetchFactory.Success policy before
  instruction : LeaInstruction
  afterCompute : MachineState
  receipt : LeaNormal before fetched.after afterCompute instruction
  fetch_exact : receipt.execution.fetch = fetched.dispatched.fetch

namespace LeaSuccess
def result {policy : CpuAccessPolicy} {before : State}
    (success : LeaSuccess policy before) : State := success.receipt.result
end LeaSuccess

def leaFromFetched {policy : CpuAccessPolicy} (before : State)
    (fetched : FetchFactory.Success policy before) : Except Failure (LeaSuccess policy before) :=
  let site := fetched.dispatched.fetch
  match selected : fetched.dispatched.selection.instruction with
  | .lea instruction =>
      match RunFactory.accessFree site.run.policy fetched.after site.run.context
          site.run.contextKind site.run.cause with
      | .error reason =>
          .error (.accessFreeRejected { before with machine := fetched.after } reason)
      | .ok computed =>
          let receipt : LeaNormal before fetched.after computed.1 instruction :=
            { execution := execution fetched computed.2.ran
              encoding := by
                have exact := fetched.dispatched.selection.encoding_eq
                rw [selected] at exact
                change instruction.encoding? = some site.site.encoding
                simpa [Instruction.encoding?] using exact }
          .ok
            { fetched := fetched
              instruction := instruction
              afterCompute := computed.1
              receipt := receipt
              fetch_exact := rfl }
  | instruction => .error (.unsupported { before with machine := fetched.after } instruction)

def lea (policy : CpuAccessPolicy) (before : State) : Except Failure (LeaSuccess policy before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched => leaFromFetched before fetched

end Grass.ISA.X86.Execution.BodyComputationFactory
