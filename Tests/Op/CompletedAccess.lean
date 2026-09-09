import Grass.Op.CompletedAccess
import Grass.Op.Completion
import Tests.Op.FakeIsa

namespace Grass.Tests.Op.CompletedAccess

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Tests.FakeIsa

private def before : MachineState := state₀.noteContext thread₀ .thread

private def descriptor : AccessDescriptor :=
  acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false

-- The concrete fixture supplies the same prepared access and complete answer
-- used by the actual Alpha.load transition.
example : ∃ resolved : before.memory.ResolvedAccess descriptor.provenance descriptor.range,
    prepareAccess before.memory descriptor = .ok resolved := by
  refine ⟨_, rfl⟩

example : ∃ (resolved : before.memory.ResolvedAccess descriptor.provenance descriptor.range)
    (complete : CompleteCommitted descriptor),
    prepareAccess before.memory descriptor = .ok resolved ∧
    policy.oracle.answerResolved before descriptor resolved = some complete := by
    refine ⟨_, _, rfl, rfl⟩

-- Instantiating ran_clean_singleton_event for the actual load produces a
-- certified appended completed-read event with the exact descriptor and counts.
example : ∃ (after : MachineState) (valid : ValidMemoryEvent),
    stepAlpha state₀ .load = .ran after ∧
    after.events = before.events ++ [valid] ∧
    valid.event.context.id = thread₀ ∧ valid.event.provenance = descriptor.provenance ∧
    valid.event.range = descriptor.range ∧
    valid.event.status = .completed 8 0 := by
  obtain ⟨resolved, complete, prepared, answered⟩ :
      ∃ (resolved : before.memory.ResolvedAccess descriptor.provenance descriptor.range)
        (complete : CompleteCommitted descriptor),
        prepareAccess before.memory descriptor = .ok resolved ∧
        policy.oracle.answerResolved before descriptor resolved = some complete := by
    refine ⟨_, _, rfl, rfl⟩
  obtain ⟨after, ran⟩ : ∃ after, stepAlpha state₀ .load = .ran after := by
    refine ⟨_, rfl⟩
  have clean : after.violations.IsEmpty := by
    have hstate : (stepAlpha state₀ .load).state? = some after := by
      simp [StepOutcome.state?, ran]
    obtain ⟨loaded, hloaded, _, hclean⟩ := load_runs
    rw [hloaded] at hstate
    cases Option.some.inj hstate
    exact hclean
  obtain ⟨space, valid, found, event, appended, supply, faults, violations⟩ :=
    ran_clean_singleton_event policy state₀
    (SomeOperation.of Alpha.load) thread₀ .thread ⟨⟨"alpha"⟩⟩ (fun _ => .none)
    ((SomeOperation.of Alpha.load).facets.substeps?.getD SubstepSequence.none_) descriptor after
    (by rfl) (by rfl) (by rfl) ran resolved prepared complete answered clean
  refine ⟨after, valid, ran, ?_, ?_, ?_, ?_, ?_⟩
  · change after.events = state₀.events ++ [valid]
    exact appended
  · exact (completedEvent_fields event).2.1
  · exact (completedEvent_fields event).2.2.2.1
  · exact (completedEvent_fields event).2.2.2.2.1
  · have readCount : complete.committed.readCount = 8 := by
      calc
        complete.committed.readCount = descriptor.range.size := complete.readsFull (by rfl)
        _ = 8 := rfl
    have writeCount : complete.committed.writeCount = 0 := by
      simp [Committed.writeCount, complete.committed.writtenAbsent (by rfl)]
    simpa [readCount, writeCount] using (completedEvent_fields event).2.2.2.2.2.2.1

-- A denied access can still return `.ran`; it has no event and a nonempty
-- violation ledger, so the `clean` premise above cannot be omitted.
example : ∃ after, stepAlpha state₀ .staleEpoch = .ran after ∧
    after.events = [] ∧ ¬ after.violations.IsEmpty := by
  refine ⟨_, rfl, by decide, by decide⟩

end Grass.Tests.Op.CompletedAccess
