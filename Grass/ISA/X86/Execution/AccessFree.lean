import Grass.ISA.X86.Execution.Fetch

/-!
# Access-free instruction completion

`AccessFree` joins an actual fetched site to an actual operation step with no
data substeps. `AccessFree.ran` uses the fetch policy, context, context kind and
cause for the following operation step.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

/-- A continuous fetched instruction followed by an access-free normal step. -/
structure AccessFree (before : State) (afterFetch afterCompute : MachineState) where
  fetch : FetchedSite before afterFetch
  operation : SomeOperation
  sequence : SubstepSequence
  selected : operation.facets.substeps? = some sequence
  noDataSubsteps : sequence.substeps = []
  faultAt : (sequence : SubstepSequence) → FaultPlan sequence
  noFault : faultAt sequence = .none
  ran : step fetch.run.policy afterFetch operation fetch.run.context fetch.run.contextKind
    fetch.run.cause faultAt = .ran afterCompute

namespace AccessFree

theorem machine_exact {before : State} {afterFetch afterCompute : MachineState}
    (receipt : AccessFree before afterFetch afterCompute) :
    afterCompute = afterFetch.noteContext receipt.fetch.run.context receipt.fetch.run.contextKind :=
  ran_accessFree_noFault_eq_noteContext receipt.fetch.run.policy afterFetch receipt.operation
    receipt.fetch.run.context receipt.fetch.run.contextKind receipt.fetch.run.cause receipt.faultAt
    receipt.sequence afterCompute receipt.selected
    (by simp [SubstepSequence.accesses, receipt.noDataSubsteps]) receipt.noFault receipt.ran

theorem state_frame {before : State} {afterFetch afterCompute : MachineState}
    (receipt : AccessFree before afterFetch afterCompute) :
    afterCompute.memory = before.machine.memory ∧
      afterCompute.obligations = before.machine.obligations := by
  rw [receipt.machine_exact]
  exact receipt.fetch.state_frame

theorem storage_frame {before : State} {afterFetch afterCompute : MachineState}
    (receipt : AccessFree before afterFetch afterCompute) :
    afterCompute.memory.allocations = before.machine.memory.allocations ∧
      afterCompute.memory.backings = before.machine.memory.backings := by
  rw [receipt.machine_exact]
  exact receipt.fetch.storage_frame

theorem events_frame {before : State} {afterFetch afterCompute : MachineState}
    (receipt : AccessFree before afterFetch afterCompute) :
    afterCompute.events = afterFetch.events := by
  rw [receipt.machine_exact]
  rfl

theorem fetched_event {before : State} {afterFetch afterCompute : MachineState}
    (receipt : AccessFree before afterFetch afterCompute) :
    ∃ valid, afterCompute.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some receipt.fetch.site.encoding.toBytes ∧
      valid.event.status = .completed receipt.fetch.site.encoding.size 0 := by
  rw [receipt.events_frame]
  exact receipt.fetch.completed_event

end AccessFree
end Grass.ISA.X86.Execution
