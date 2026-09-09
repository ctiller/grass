import Grass.Platform.Win32.WriteFileReturn
import Tests.Platform.Win32WriteFile

/-! An actual bookkeeping return under an explicitly synthetic interpretation.
This challenges wrapper composition, not physical Windows adequacy. -/
namespace Grass.Tests.Win32MatchedReturn

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.WriteFile Grass.Tests.Win32WriteFile

def model : CausalModel := ⟨fun state a b =>
  a = .entry call ∧ b = .returned call ∧ Represented state a ∧ Represented state b⟩

theorem model_valid (state : CallProtocol.State Request) : model.Valid state where
  endpoints := by intro a b h; exact ⟨h.2.2.1, h.2.2.2⟩
  irreflexive := by intro node h; have bad := h.1.symm.trans h.2.1; cases bad
  transitive := by
    intro a b c hab hbc
    have bad := hab.2.1.symm.trans hbc.1
    cases bad

def realized : Realization := { noEffects with causal := model }

theorem no_return_pending : ¬ Represented pending (.returned call) := by
  rintro ⟨caller, agent, loans, member⟩
  change CallProtocol.Boundary.returned call caller agent loans ∈
    [.handoff call record.caller record.agent record.ids] at member
  simp at member

theorem no_return_initial : ¬ Represented initial (.returned call) := by
  rintro ⟨caller, agent, loans, member⟩
  change _ ∈ [] at member
  contradiction

def reached : History realized initial call record initialPrefix :=
  .handoff initialPrefix rfl prepared {
    beforeValid := model_valid initial
    afterValid := model_valid pending
    historyExtends := by
      intro a b h
      exact False.elim (no_return_initial (h.2.1 ▸ h.2.2.2))
    entry := List.mem_cons_self
    callerEntry := by intro old member; change old ∈ [] at member; contradiction } rfl

def attempt := CallProtocol.return? pending call record.caller record.agent record.ids
def returnedState := (attempt.get (by decide)).2
def rawFailure : ReturnResult := ⟨0, none⟩

def interpretation : ReturnInterpretation := fun _ selected selectedRecord before after accepted result =>
  selected = call ∧ selectedRecord = record ∧ before = pending ∧ after = returnedState ∧
    accepted = 0 ∧ result = rawFailure

theorem matched : MatchedReturn interpretation reached rawFailure returnedState where
  ran := rfl
  interpreted := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  conforms := rfl
  causal := {
    fresh := no_return_pending
    valid := model_valid returnedState
    historyExtends := by
      intro a b h
      exact False.elim (no_return_pending (h.2.1 ▸ h.2.2.2))
    entryReturn := ⟨rfl, rfl,
      ⟨record.caller, record.agent, record.ids, List.mem_cons_self⟩,
      ⟨record.caller, record.agent, record.ids, List.mem_cons_of_mem _ List.mem_cons_self⟩⟩
    effectsReturn := by intro event member; change event ∈ [] at member; contradiction }

example : returnedState.pending.lookup call = none := matched.consumed.1
example : CallProtocol.return? returnedState call record.caller record.agent record.ids = none :=
  matched.consumed.2.2.1

example : ¬ MatchedReturn (fun _ _ _ _ _ _ _ => False) reached rawFailure returnedState := by
  intro impossible
  exact impossible.interpreted

example : ¬ ReturnCausality startHistory returnedState := by
  intro impossible
  exact impossible.entryReturn

end Grass.Tests.Win32MatchedReturn
