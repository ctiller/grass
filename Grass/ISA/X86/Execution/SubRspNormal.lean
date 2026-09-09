import Grass.ISA.X86.Execution.Fetch
import Grass.ISA.X86.Execution.StackInstruction
import Grass.ISA.X86.Execution.CompletionFlags

/-!
# The bounded normal SUB RSP completion branch

This constructor joins one actual fetched instruction to an actual access-free
operation result, under the same policy, context and cause. The decoded typed
immediate selects the production arithmetic and full-RFLAGS normal transfer.
It is a conditional normal branch, not a total execution relation: failure to
construct this receipt never excludes faults, traps or interruptions.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

/-- Inputs to the normal branch, with a continuous fetch-to-compute machine run. -/
structure SubRspNormal (before : State) (afterFetch afterCompute : MachineState)
    (immediate : ImmediateArithmetic.Immediate) where
  fetch : FetchedSite before afterFetch
  encoding : fetch.site.encoding = (StackInstruction.subRsp immediate).encoding
  operation : SomeOperation
  sequence : SubstepSequence
  selected : operation.facets.substeps? = some sequence
  /-- SUB RSP has no data-memory or faulting compute substeps in this normal branch. -/
  noDataSubsteps : sequence.substeps = []
  faultAt : (sequence : SubstepSequence) → FaultPlan sequence
  noFault : faultAt sequence = .none
  ran : step fetch.run.policy afterFetch operation fetch.run.context fetch.run.contextKind
    fetch.run.cause faultAt = .ran afterCompute

namespace SubRspNormal

/-- `fetched_event` connects this typed SUB to the bytes of the actual fetch. -/
theorem fetched_event {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) :
    ∃ valid, afterFetch.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some (StackInstruction.subRsp immediate).encoding.toBytes := by
  obtain ⟨valid, appended, bytes, _⟩ := receipt.fetch.completed_event
  exact ⟨valid, appended, by simpa [receipt.encoding] using bytes⟩

/-- The normal architectural result uses the actual operation's memory machine. -/
def result {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) : State :=
  { before.withGpr .rsp
      ((RegisterSemantics.evaluateImmediate .sub .w64 (before.gpr .rsp) immediate
        before.statusFlags).destination (before.gpr .rsp)) with
    machine := afterCompute
    rip := receipt.fetch.site.fallthroughRip
    rflags := completedSubRflags before immediate }

/-- `machine_frame` derives the access-free result from the actual selected step. -/
theorem machine_frame {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) :
    afterCompute = afterFetch.noteContext receipt.fetch.run.context receipt.fetch.run.contextKind :=
  ran_accessFree_noFault_eq_noteContext receipt.fetch.run.policy afterFetch receipt.operation
    receipt.fetch.run.context receipt.fetch.run.contextKind receipt.fetch.run.cause receipt.faultAt
    receipt.sequence afterCompute receipt.selected
    (by simp [SubstepSequence.accesses, receipt.noDataSubsteps]) receipt.noFault receipt.ran

/-- `rsp_exact` uses the signed typed immediate selected by the actual encoding. -/
theorem rsp_exact {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) :
    receipt.result.gpr .rsp = before.gpr .rsp - BitVec.ofInt 64 immediate.toInt := rfl

/-- `gpr_frame` retains every register other than RSP in the normal branch. -/
theorem gpr_frame {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) (register : Gpr)
    (other : register ≠ .rsp) : receipt.result.gpr register = before.gpr register := by
  simp [result, State.withGpr, other]

/-- The next RIP comes from the whole actual fetched encoding, not a supplied size. -/
theorem rip_exact {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) :
    receipt.result.rip = receipt.fetch.site.fallthroughRip := rfl

/-- The normal full-RFLAGS rule includes RF clearing independently of status bits. -/
theorem rflags_exact {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) :
    receipt.result.rflags = completedSubRflags before immediate := rfl

/-- `storage_frame` composes the actual fetch frame and access-free operation frame. -/
theorem storage_frame {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) :
    receipt.result.machine.memory.allocations = before.machine.memory.allocations ∧
      receipt.result.machine.memory.backings = before.machine.memory.backings := by
  change afterCompute.memory.allocations = _ ∧ afterCompute.memory.backings = _
  rw [receipt.machine_frame]
  exact receipt.fetch.storage_frame

/-- `state_frame` retains both the memory authority state and the obligation ledger. -/
theorem state_frame {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) :
    receipt.result.machine.memory = before.machine.memory ∧
      receipt.result.machine.obligations = before.machine.obligations := by
  change afterCompute.memory = _ ∧ afterCompute.obligations = _
  rw [receipt.machine_frame]
  exact receipt.fetch.state_frame

/-- `events_exact` carries the typed fetch event through the access-free normal result. -/
theorem events_exact {before : State} {afterFetch afterCompute : MachineState}
    {immediate : ImmediateArithmetic.Immediate}
    (receipt : SubRspNormal before afterFetch afterCompute immediate) :
    ∃ valid, receipt.result.machine.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some (StackInstruction.subRsp immediate).encoding.toBytes := by
  change ∃ valid, afterCompute.events = _ ∧ _
  rw [receipt.machine_frame]
  exact receipt.fetched_event

end SubRspNormal
end Grass.ISA.X86.Execution
