import Grass.Assembly.Store32Execution
import Tests.Memory.Spike1Policy

/-! The resolved value is enforced through the existing Spike 1 transition. -/
namespace Grass.Tests.Assembly.Store32Execution

open Grass.Assembly Store32 Store32Execution Grass.Core Grass.Memory Grass.Op
open Grass.Tests.Spike1 Grass.Tests.Spike1Policy Tests.Memory.Spike1Block

def source : Store32.Input := ⟨"transferred", 0x01020304⟩
def slots : Store32.SlotEnv := .empty |>.insert source.slot 0
def resolved? : Option Store32.Resolved :=
  Store32.resolve? frameLayout frameBaseOffset slots source

theorem the_source_store_resolves : resolved?.isSome := by decide

theorem descriptor_range_of_resolved {resolved : Store32.Resolved}
    (h : resolved? = some resolved) : transferredWrite.range = resolved.range := by
  cases h
  decide

theorem the_derived_oracle_answers_with_exact_bytes :
    ∀ resolved, resolved? = some resolved →
      ∃ hrange : transferredWrite.range = resolved.range,
        ∃ hintent : transferredWrite.intent = .write,
          ((Store32Execution.oracle resolved transferredWrite hrange hintent).answer
            machine₀ transferredWrite).map (fun answer => answer.committed.written) =
              some (some resolved.writeBytes) := by
  intro resolved h
  have hrange : transferredWrite.range = resolved.range := by cases h; decide
  have hintent : transferredWrite.intent = .write := rfl
  exact ⟨hrange, hintent, by simp⟩

theorem the_existing_step_commits_the_resolved_value :
    ∀ resolved, ∀ h : resolved? = some resolved,
      (Store32Execution.step policy machine₀ resolved transferredWrite
        (descriptor_range_of_resolved h) rfl .thread
        ⟨⟨"resolved-store32"⟩⟩).state?.isSome ∧
      ∀ ran, (Store32Execution.step policy machine₀ resolved transferredWrite
          (descriptor_range_of_resolved h) rfl .thread
          ⟨⟨"resolved-store32"⟩⟩).state? = some ran →
        ran.violations.IsEmpty ∧
        (∀ i < 4, ran.memory.byteAt? stackAlloc (transferredRange.start + i) =
          resolved.writeBytes[i]?) ∧
        ran.events.getLast?.map (fun event => event.event.valueWritten) =
          some (some resolved.writeBytes) := by
  intro resolved h
  cases h
  refine ⟨by decide, ?_⟩
  intro ran hran
  cases hran
  exact ⟨by decide, by decide, by decide⟩

/-- The old profile oracle passes every safety check but chooses unrelated bytes;
this is the adversarial control showing why the resolved oracle must be installed. -/
theorem the_free_profile_oracle_can_commit_the_wrong_value :
    ∀ resolved, resolved? = some resolved →
      ∀ ran, (Grass.Op.step policy machine₀
          (Store32Execution.operation transferredWrite) transferredWrite.context .thread
          ⟨⟨"free-oracle-store32"⟩⟩).state? = some ran →
        ran.violations.IsEmpty ∧
        ran.memory.byteAt? stackAlloc transferredRange.start = some 0xAB ∧
        resolved.writeBytes[0]? = some 0x04 ∧
        ran.memory.byteAt? stackAlloc transferredRange.start ≠ resolved.writeBytes[0]? := by
  intro resolved h ran hran
  cases h
  cases hran
  exact ⟨by decide, by decide, by decide, by decide⟩

end Grass.Tests.Assembly.Store32Execution
