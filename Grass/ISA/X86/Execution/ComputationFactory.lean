import Grass.ISA.X86.Execution.FetchFactory
import Grass.ISA.X86.Execution.MoveNormal
import Grass.ISA.X86.Execution.RunFactory
import Grass.ISA.X86.Execution.SubRspNormal

/-!
# Constructive access-free instruction execution

`move` and `subRsp` construct their fetched normal receipts from a policy and
input state. Each function retains other decoded families as explicit
unsupported reached prefixes.
-/

namespace Grass.ISA.X86.Execution.ComputationFactory

open Grass.Memory Grass.Op

inductive Failure where
  | fetch (reason : FetchFactory.Failure)
  | unsupported (reached : State) (instruction : Instruction)
  | accessFreeRejected (reached : State) (reason : StepRejection)

structure MoveSuccess (before : State) where
  instruction : MoveInstruction
  afterFetch : MachineState
  afterCompute : MachineState
  receipt : MoveNormal before afterFetch afterCompute instruction

namespace MoveSuccess

def result {before : State} (success : MoveSuccess before) : State := success.receipt.result

end MoveSuccess

structure SubRspSuccess (before : State) where
  immediate : ImmediateArithmetic.Immediate
  afterFetch : MachineState
  afterCompute : MachineState
  receipt : SubRspNormal before afterFetch afterCompute immediate

namespace SubRspSuccess

def result {before : State} (success : SubRspSuccess before) : State := success.receipt.result

end SubRspSuccess

/-- Execute from an actual fetch for the bounded register MOV family. Every other selected
family is retained as an explicit unsupported fetched prefix. -/
def moveFromFetched {policy : CpuAccessPolicy} (before : State)
    (fetched : FetchFactory.Success policy before) : Except Failure (MoveSuccess before) :=
      let site := fetched.dispatched.fetch
      match selected : fetched.dispatched.selection.instruction with
      | .move instruction =>
          match RunFactory.accessFree site.run.policy fetched.after site.run.context
              site.run.contextKind site.run.cause with
          | .error reason =>
              .error (.accessFreeRejected { before with machine := fetched.after } reason)
          | .ok computed =>
              let execution : AccessFree before fetched.after computed.1 :=
                { fetch := site
                  operation := RunFactory.accessFreeOperation
                  sequence := .none_
                  selected := rfl
                  noDataSubsteps := rfl
                  faultAt := RunFactory.noFaultPlan
                  noFault := rfl
                  ran := computed.2.ran }
              let receipt : MoveNormal before fetched.after computed.1 instruction :=
                { execution := execution
                  encoding := by
                    have exact := fetched.dispatched.selection.encoding_eq
                    rw [selected] at exact
                    exact (Option.some.inj exact).symm }
              .ok
                { instruction := instruction
                  afterFetch := fetched.after
                  afterCompute := computed.1
                  receipt := receipt }
      | instruction =>
          .error (.unsupported { before with machine := fetched.after } instruction)

def move (policy : CpuAccessPolicy) (before : State) : Except Failure (MoveSuccess before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched => moveFromFetched before fetched

/-- Execute the typed `SUB RSP, immediate` from its actual fetched receipt. -/
def subRspFromFetched {policy : CpuAccessPolicy} (before : State)
    (fetched : FetchFactory.Success policy before) : Except Failure (SubRspSuccess before) :=
      let site := fetched.dispatched.fetch
      match selected : fetched.dispatched.selection.instruction with
      | .stack (.subRsp immediate) =>
          match RunFactory.accessFree site.run.policy fetched.after site.run.context
              site.run.contextKind site.run.cause with
          | .error reason =>
              .error (.accessFreeRejected { before with machine := fetched.after } reason)
          | .ok computed =>
              let receipt : SubRspNormal before fetched.after computed.1 immediate :=
                { fetch := site
                  encoding := by
                    have exact := fetched.dispatched.selection.encoding_eq
                    rw [selected] at exact
                    exact (Option.some.inj exact).symm
                  operation := RunFactory.accessFreeOperation
                  sequence := .none_
                  selected := rfl
                  noDataSubsteps := rfl
                  faultAt := RunFactory.noFaultPlan
                  noFault := rfl
                  ran := computed.2.ran }
              .ok
                { immediate := immediate
                  afterFetch := fetched.after
                  afterCompute := computed.1
                  receipt := receipt }
      | instruction =>
          .error (.unsupported { before with machine := fetched.after } instruction)

def subRsp (policy : CpuAccessPolicy) (before : State) :
    Except Failure (SubRspSuccess before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched => subRspFromFetched before fetched

end Grass.ISA.X86.Execution.ComputationFactory
