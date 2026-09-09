import Grass.ISA.X86.Execution.FetchAttempt
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionFetchAttempt

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def before : State :=
  { machine := state₀, gpr := fun _ => 0, rip := 0x1000, rflags := 0 }
private def descriptor : AccessDescriptor :=
  acc bufferProv ⟨0, 2⟩ 0x1000 .execute .readExecute true false
private inductive IncompleteFetch where | fetch
private instance : HasOperationFacets IncompleteFetch where
  facets
    | .fetch =>
      { memoryEffects := some (.single descriptor), faults := none
        restartability := some .restartable, ordering := some .plain }

private def reason : StepRejection := .facetsNotClosed .faults

example : ∃ attempt : FetchAttempt before (.rejected reason),
    step attempt.policy before.machine attempt.operation attempt.context attempt.contextKind
      attempt.cause attempt.faultAt = StepOutcome.rejected reason ∧
      StepOutcome.rejection? (.rejected reason) = some reason := by
  let attempt : FetchAttempt before (.rejected reason) :=
    { policy := policy, operation := SomeOperation.of IncompleteFetch.fetch
      context := thread₀, contextKind := .thread, cause := ⟨⟨"fetch-attempt"⟩⟩
      faultAt := fun _ => .none, descriptor := descriptor, sequence := .single descriptor
      selected := by rfl, substeps_exact := by rfl, contextExact := by rfl
      intent := by rfl, initialization := by rfl, ledgerEffect := by rfl
      authorityEffect := by rfl, address := by rfl, actual := by rfl }
  exact ⟨attempt, attempt.rejected, rfl⟩

end Grass.Tests.ISA.X86.ExecutionFetchAttempt
