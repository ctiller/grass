import Grass.ISA.X86.Execution.FetchFactory
import Grass.ISA.X86.Execution.MoveNormal
import Grass.ISA.X86.Execution.RunFactory

/-!
# Constructive fetched MOV execution

`move` constructs the fetched normal MOV receipt from a policy and input state.
Other decoded families remain explicit unsupported reached prefixes.
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

/-- Fetch and execute only the bounded register MOV family. Every other selected
family is retained as an explicit unsupported fetched prefix. -/
def move (policy : CpuAccessPolicy) (before : State) : Except Failure (MoveSuccess before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched =>
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

end Grass.ISA.X86.Execution.ComputationFactory
