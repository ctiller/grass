import Grass.Platform.Win32.RawServicePrefix
import Tests.Platform.Win32RawServiceContinuation

/-! Two actual checked service edges, with no admissible third service edge.
This exercises finite history extraction on the existing five-loan fixture;
it supplies no native CALL, infinite execution, or provider-return claim. -/

namespace Grass.Tests.Win32RawServicePrefix

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader Grass.Platform.Win32.Raw
open Grass.Tests.Win32RawStep Grass.Tests.Win32RawServiceContinuation
open Grass.Tests.Win32WriteFileService

def original : History runtime.loanPlan Grass.Tests.Win32WriteFile.noEffects
    Grass.Tests.Win32WriteFile.initial call record prefix₀ :=
  .handoff prefix₀ rfl Grass.Tests.Win32WriteFile.prepared {
    beforeValid := Grass.Tests.Win32WriteFile.noEffects_valid _
    afterValid := Grass.Tests.Win32WriteFile.noEffects_valid _
    historyExtends := by intro _ _ impossible; exact False.elim impossible
    entry := List.mem_cons_self
    callerEntry := by intro old present; change old ∈ [] at present; contradiction } rfl

def raw : Nat → RawState
  | 0 => before
  | 1 => receipt₁.after
  | 2 => receipt₂.after
  | _ => { receipt₂.after with control := .terminal call 0 }

theorem two_steps {image : ImageInput} {inputs : EntryInputs} (loaded : LoadedImage image inputs) :
    ∀ n, n < 2 → RawStep loaded Grass.Tests.Win32WriteFile.noEffects
      Grass.Tests.Win32WriteFileConsolePublication.environment noReturnInterpretation
      [] (raw n) (.providerService call record.agent action) quietEvent (raw (n + 1)) [] := by
  intro n below
  cases n with
  | zero => exact quiet_service loaded
  | succ n =>
    have zero : n = 0 := by omega
    subst n
    exact quiet_service₂ loaded

noncomputable def folded {image : ImageInput} {inputs : EntryInputs} (loaded : LoadedImage image inputs) :=
  RawStep.foldServicePrefix raw (fun _ => []) (fun _ => record.agent) (fun _ => action)
    (fun _ => quietEvent) 2 (two_steps loaded) original receipt₁.projected runtime rfl rfl rfl

/-- The finite fold reaches the actual second protocol and runtime frontier. -/
theorem endpoint {image : ImageInput} {inputs : EntryInputs} (loaded : LoadedImage image inputs) :
    (folded loaded).1 = protocol₂ ∧ (folded loaded).2.1.accepted = 0 := by
  have projected := (folded loaded).2.2.property.1
  have actual := receipt₂.after_projected
  have sameState : (folded loaded).1 = protocol₂ := Option.some.inj (projected.symm.trans actual)
  obtain ⟨currentRuntime, lookup, _, accepted⟩ := (folded loaded).2.2.property.2
  have sameRuntime : currentRuntime = receipt₂.nextRuntime :=
    CallRuntime.writeFile.inj (Option.some.inj (lookup.symm.trans receipt₂.after_runtimeLookup))
  exact ⟨sameState, accepted.symm.trans (congrArg WriteFileRuntime.accepted sameRuntime)⟩

theorem no_third_edge {image : ImageInput} {inputs : EntryInputs} (loaded : LoadedImage image inputs) :
    ¬ RawStep loaded Grass.Tests.Win32WriteFile.noEffects
      Grass.Tests.Win32WriteFileConsolePublication.environment noReturnInterpretation
      [] (raw 2) (.providerService call record.agent action) quietEvent (raw 3) [] := by
  intro step
  obtain ⟨_, _, service, _, afterExact, _, _, _⟩ := step.service_receipt
  have control := service.after_control
  rw [afterExact] at control
  cases control

end Grass.Tests.Win32RawServicePrefix
