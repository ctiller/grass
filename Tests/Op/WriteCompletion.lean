import Grass.Op.WriteCompletion
import Tests.Op.FakeIsa

namespace Grass.Tests.Op.WriteCompletion

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Tests.FakeIsa

private def before : MachineState := state₀.noteContext thread₀ .thread

private def descriptor : AccessDescriptor :=
  acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite false true

-- The concrete memory oracle's successful store answer exposes its exact
-- supplied prefix, rather than merely a full-width anonymous write.
example : ∃ (resolved : before.memory.ResolvedAccess descriptor.provenance descriptor.range)
    (complete : CompleteCommitted descriptor),
    prepareAccess before.memory descriptor = .ok resolved ∧
    policy.oracle.answerResolved before descriptor resolved = some complete ∧
    complete.committed.written = some ((storedBytes before descriptor).take descriptor.range.size) := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  exact Oracle.ofMemory_written_of_answerResolved storedBytes indeterminateByte before descriptor
    _ _ rfl rfl

-- The actual Alpha.store transition is reduced to `commitResolved`; the result
-- is obtained from the selected operation and clean ledger, not asserted as an
-- arbitrary post-state.
example : ∃ (after : MachineState)
    (resolved : before.memory.ResolvedAccess descriptor.provenance descriptor.range)
    (complete : CompleteCommitted descriptor),
    stepAlpha state₀ .store = .ran after ∧
    after.memory = state₀.memory.commitResolved descriptor resolved complete.committed.written
      complete.committed.writtenFits := by
  obtain ⟨resolved, complete, prepared, answered⟩ :
      ∃ (resolved : before.memory.ResolvedAccess descriptor.provenance descriptor.range)
        (complete : CompleteCommitted descriptor),
        prepareAccess before.memory descriptor = .ok resolved ∧
        policy.oracle.answerResolved before descriptor resolved = some complete := by
    refine ⟨_, _, rfl, rfl⟩
  obtain ⟨after, ranStep⟩ : ∃ after, stepAlpha state₀ .store = .ran after := by
    refine ⟨_, rfl⟩
  have clean : after.violations.IsEmpty := by
    have outcome : (stepAlpha state₀ .store).state? = some after := by
      simp [StepOutcome.state?, ranStep]
    obtain ⟨stored, hstored, hclean⟩ := store_runs
    rw [hstored] at outcome
    cases Option.some.inj outcome
    exact hclean
  have ran : step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ = .ran after := ranStep
  have selected : (SomeOperation.of Alpha.store).facets.substeps? =
      some (.single descriptor) := by rfl
  obtain ⟨space, found, wellFormed⟩ := ran_selected_access_wellFormed policy state₀
    (SomeOperation.of Alpha.store) thread₀ .thread ⟨⟨"alpha"⟩⟩ (fun _ => .none)
    (.single descriptor) after descriptor selected ran (by
      change descriptor ∈ [descriptor]
      simp)
  have performed := ran_singleton_prepared_eq_performPreparedAccess policy state₀
    (SomeOperation.of Alpha.store) thread₀ .thread ⟨⟨"alpha"⟩⟩ (fun _ => .none)
    (.single descriptor) descriptor after selected (by rfl) (by rfl) ran resolved prepared complete answered
  refine ⟨after, resolved, complete, ranStep, ?_⟩
  exact clean_prepared_complete_memory_eq_commitResolved policy before after descriptor
    resolved prepared complete .thread ⟨⟨"alpha"⟩⟩ space found wellFormed performed clean rfl rfl

end Grass.Tests.Op.WriteCompletion
