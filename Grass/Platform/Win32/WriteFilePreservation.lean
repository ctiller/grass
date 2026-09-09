import Grass.Platform.Win32.WriteFileReturn

/-!
# `WriteFile` custody preservation

The protocol handoff changes authority records only, and each provider step is
explicitly confined by its fixed `LoanPlan`.  This module joins those facts over
a reached history; it makes no claim about a physical call or return instruction.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86

/-- `History.cellAt?_preserved` proves preservation of every cell outside its fixed writable
custody boundary. -/
theorem History.cellAt?_preserved {plan : LoanPlan} {realization : Realization}
    {initial : ProtocolState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {state : ProtocolState}
    {frontier : Prefix plan state call record}
    (history : History plan realization initial call record frontier) (root : AllocId)
    (offset : Nat) (notWritable : ¬ plan.WriteAt record.request root offset) :
    state.machine.memory.cellAt? root offset = initial.machine.memory.cellAt? root offset := by
  induction history with
  | handoff frontier ran input causal zero =>
      obtain ⟨memory, issued, machine⟩ := (CallProtocol.handoff?_records ran).2.2.2.2.2
      rw [machine]
      exact MemoryState.cellAt?_of_maps_eq (LoanBatch.allocations_issue? issued)
        (LoanBatch.backings_issue? issued) root offset
  | step previous action output committed ih =>
      exact (committed.confined root offset notWritable).trans ih

/-- `MatchedReturn.cellAt?_preserved` proves preservation of every cell framed by the reached
provider history. -/
theorem MatchedReturn.cellAt?_preserved {plan : LoanPlan} {selected : ReturnInterpretation}
    {realization : Realization} {initial : ProtocolState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {before after : ProtocolState}
    {frontier : Prefix plan before call record}
    {history : History plan realization initial call record frontier} {result : ReturnResult}
    (returned : MatchedReturn selected history result after) (root : AllocId) (offset : Nat)
    (notWritable : ¬ plan.WriteAt record.request root offset) :
    after.machine.memory.cellAt? root offset = initial.machine.memory.cellAt? root offset :=
  (returned.effects.cells_unchanged root offset).trans
    (history.cellAt?_preserved root offset notWritable)

namespace Abi

/-- The observed return-address bytes remain unchanged throughout a reached
provider history when the protocol plan and request are the actual ABI plan and
request.  `initialMachine` is the explicit bridge from the actual CPU state to
the protocol state. -/
theorem StackPlan.return_cellAt?_preserved {plan : LoanPlan} {realization : Realization}
    {initial : ProtocolState} {initialCPU : Execution.State} {request : Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request} {state : ProtocolState}
    {frontier : Prefix plan state call record} (stack : StackPlan initialCPU request)
    (initialMachine : initialCPU.machine = initial.machine) (planExact : plan = stack.loanPlan)
    (requestExact : record.request = request)
    (history : History plan realization initial call record frontier) (i : Fin 8) :
    state.machine.memory.cellAt? stack.returnSlot.provenance.root
      (stack.returnSlot.range.start + i.val) =
      initialCPU.machine.memory.cellAt? stack.returnSlot.provenance.root
        (stack.returnSlot.range.start + i.val) := by
  rw [initialMachine]
  apply history.cellAt?_preserved
  rw [planExact, requestExact]
  exact stack.returnProtected i

/-- The nullable fifth-argument bytes remain unchanged throughout a reached
provider history under the same explicit ABI/protocol correspondence. -/
theorem StackPlan.overlapped_cellAt?_preserved {plan : LoanPlan}
    {realization : Realization} {initial : ProtocolState} {initialCPU : Execution.State}
    {request : Request} {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    (stack : StackPlan initialCPU request) (initialMachine : initialCPU.machine = initial.machine)
    (planExact : plan = stack.loanPlan) (requestExact : record.request = request)
    (history : History plan realization initial call record frontier) (i : Fin 8) :
    state.machine.memory.cellAt? stack.entry.overlappedSlot.provenance.root
      (stack.entry.overlappedSlot.range.start + i.val) =
      initialCPU.machine.memory.cellAt? stack.entry.overlappedSlot.provenance.root
        (stack.entry.overlappedSlot.range.start + i.val) := by
  rw [initialMachine]
  apply history.cellAt?_preserved
  rw [planExact, requestExact]
  exact stack.overlappedProtected i

/-- `StackPlan.return_cellAt?_preserved_after_return` proves preservation of the observed return-address bytes.
This is a protocol-state result, not a physical `RET` claim. -/
theorem StackPlan.return_cellAt?_preserved_after_return {plan : LoanPlan}
    {selected : ReturnInterpretation} {realization : Realization} {initial : ProtocolState}
    {initialCPU : Execution.State} {request : Request} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {before after : ProtocolState}
    {frontier : Prefix plan before call record} (stack : StackPlan initialCPU request)
    (initialMachine : initialCPU.machine = initial.machine) (planExact : plan = stack.loanPlan)
    (requestExact : record.request = request)
    (history : History plan realization initial call record frontier) {result : ReturnResult}
    (returned : MatchedReturn selected history result after) (i : Fin 8) :
    after.machine.memory.cellAt? stack.returnSlot.provenance.root
      (stack.returnSlot.range.start + i.val) =
      initialCPU.machine.memory.cellAt? stack.returnSlot.provenance.root
        (stack.returnSlot.range.start + i.val) := by
  rw [initialMachine]
  apply returned.cellAt?_preserved
  rw [planExact, requestExact]
  exact stack.returnProtected i

/-- `StackPlan.overlapped_cellAt?_preserved_after_return` proves preservation of the nullable fifth-argument bytes.
This is a protocol-state result, not a physical `RET` claim. -/
theorem StackPlan.overlapped_cellAt?_preserved_after_return {plan : LoanPlan}
    {selected : ReturnInterpretation} {realization : Realization} {initial : ProtocolState}
    {initialCPU : Execution.State} {request : Request} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {before after : ProtocolState}
    {frontier : Prefix plan before call record} (stack : StackPlan initialCPU request)
    (initialMachine : initialCPU.machine = initial.machine) (planExact : plan = stack.loanPlan)
    (requestExact : record.request = request)
    (history : History plan realization initial call record frontier) {result : ReturnResult}
    (returned : MatchedReturn selected history result after) (i : Fin 8) :
    after.machine.memory.cellAt? stack.entry.overlappedSlot.provenance.root
      (stack.entry.overlappedSlot.range.start + i.val) =
      initialCPU.machine.memory.cellAt? stack.entry.overlappedSlot.provenance.root
        (stack.entry.overlappedSlot.range.start + i.val) := by
  rw [initialMachine]
  apply returned.cellAt?_preserved
  rw [planExact, requestExact]
  exact stack.overlappedProtected i

end Abi
end Grass.Platform.Win32.WriteFile
