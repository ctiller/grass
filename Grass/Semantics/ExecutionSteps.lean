import Grass.Semantics.Execution

/-! Indexed witnesses recovered propositionally from an admitted finite derivation. -/

namespace Grass.RelationalSystem

universe u

/-- A coherent finite derivation admits state, graph, and choice witnesses at
every trace index.  The witnesses need not be unique and this theorem does not
choose a canonical execution independently of the supplied `Steps` proof. -/
theorem Steps.exists_indexed_witnesses {Event : Type u}
    {system : RelationalSystem Event}
    {start finish : system.State} {startGraph finishGraph : system.Graph}
    {events : List Event}
    (steps : system.Steps start startGraph events finish finishGraph) :
    ∃ (states : Fin (events.length + 1) → system.State)
      (graphs : Fin (events.length + 1) → system.Graph)
      (choices : Fin events.length → system.Choice),
      states ⟨0, Nat.zero_lt_succ _⟩ = start ∧
      graphs ⟨0, Nat.zero_lt_succ _⟩ = startGraph ∧
      states ⟨events.length, Nat.lt_succ_self _⟩ = finish ∧
      graphs ⟨events.length, Nat.lt_succ_self _⟩ = finishGraph ∧
      ∀ index : Fin events.length,
        system.Step (graphs index.castSucc) (states index.castSucc) (choices index)
          (events.get index) (states index.succ) (graphs index.succ) := by
  induction steps with
  | refl =>
      refine ⟨fun _ => start, fun _ => startGraph, Fin.elim0, rfl, rfl, rfl, rfl, ?_⟩
      intro index
      exact Fin.elim0 index
  | @step priorEvents current currentGraph choice event next nextGraph prior transition ih =>
      obtain ⟨states, graphs, choices, stateZero, graphZero, stateLast, graphLast,
        transitions⟩ := ih
      let nextStates : Fin ((priorEvents ++ [event]).length + 1) → system.State :=
        fun index => Fin.lastCases next states (Fin.cast (by simp) index)
      let nextGraphs : Fin ((priorEvents ++ [event]).length + 1) → system.Graph :=
        fun index => Fin.lastCases nextGraph graphs (Fin.cast (by simp) index)
      let nextChoices : Fin (priorEvents ++ [event]).length → system.Choice :=
        fun index => Fin.lastCases choice choices (Fin.cast (by simp) index)
      have nextStates_cast (index : Fin (priorEvents.length + 1)) :
          nextStates (Fin.cast (by simp) index.castSucc) = states index := by
        simp [nextStates]
      have nextGraphs_cast (index : Fin (priorEvents.length + 1)) :
          nextGraphs (Fin.cast (by simp) index.castSucc) = graphs index := by
        simp [nextGraphs]
      have nextChoices_cast (index : Fin priorEvents.length) :
          nextChoices (Fin.cast (by simp) index.castSucc) = choices index := by
        simp [nextChoices]
      have nextChoices_last :
          nextChoices (Fin.cast (by simp) (Fin.last priorEvents.length)) = choice := by
        simp [nextChoices]
      have nextStates_last :
          nextStates (Fin.cast (by simp) (Fin.last (priorEvents.length + 1))) = next := by
        simp [nextStates]
      have nextGraphs_last :
          nextGraphs (Fin.cast (by simp) (Fin.last (priorEvents.length + 1))) = nextGraph := by
        simp [nextGraphs]
      refine ⟨nextStates, nextGraphs, nextChoices, ?_, ?_, ?_, ?_, ?_⟩
      · change Fin.lastCases next states _ = start
        rw [show (Fin.cast (by simp) ⟨0, Nat.zero_lt_succ _⟩) =
          (⟨0, Nat.zero_lt_succ _⟩ : Fin (priorEvents.length + 1)).castSucc by ext; rfl,
          Fin.lastCases_castSucc]
        exact stateZero
      · change Fin.lastCases nextGraph graphs _ = startGraph
        rw [show (Fin.cast (by simp) ⟨0, Nat.zero_lt_succ _⟩) =
          (⟨0, Nat.zero_lt_succ _⟩ : Fin (priorEvents.length + 1)).castSucc by ext; rfl,
          Fin.lastCases_castSucc]
        exact graphZero
      · change Fin.lastCases next states _ = next
        rw [show (Fin.cast (by simp) ⟨(priorEvents ++ [event]).length,
          Nat.lt_succ_self _⟩) = Fin.last (priorEvents.length + 1) by ext; simp,
          Fin.lastCases_last]
      · change Fin.lastCases nextGraph graphs _ = nextGraph
        rw [show (Fin.cast (by simp) ⟨(priorEvents ++ [event]).length,
          Nat.lt_succ_self _⟩) = Fin.last (priorEvents.length + 1) by ext; simp,
          Fin.lastCases_last]
      · intro index
        let castIndex : Fin (priorEvents.length + 1) := Fin.cast (by simp) index
        have indexEq : index = Fin.cast (by simp) castIndex := by ext; rfl
        rw [indexEq]
        refine Fin.lastCases ?_ (fun earlier => ?_) castIndex
        · have inputEq :
              (Fin.cast (by simp) (Fin.last priorEvents.length)).castSucc =
                (Fin.cast (by simp) (Fin.last priorEvents.length).castSucc :
                  Fin ((priorEvents ++ [event]).length + 1)) := by
              ext
              rfl
          have outputEq :
              (Fin.cast (by simp) (Fin.last priorEvents.length)).succ =
                (Fin.cast (by simp) (Fin.last (priorEvents.length + 1)) :
                  Fin ((priorEvents ++ [event]).length + 1)) := by
              ext
              simp
          have stateAtLast : states (Fin.last priorEvents.length) = current := by
            rw [show Fin.last priorEvents.length =
              (⟨priorEvents.length, Nat.lt_succ_self _⟩ : Fin (priorEvents.length + 1)) by
                ext
                simp]
            exact stateLast
          have graphAtLast : graphs (Fin.last priorEvents.length) = currentGraph := by
            rw [show Fin.last priorEvents.length =
              (⟨priorEvents.length, Nat.lt_succ_self _⟩ : Fin (priorEvents.length + 1)) by
                ext
                simp]
            exact graphLast
          rw [inputEq, outputEq, nextGraphs_cast, nextStates_cast, nextChoices_last,
            nextStates_last, nextGraphs_last, stateAtLast, graphAtLast]
          simpa using transition
        · have inputEq : (Fin.cast (by simp) earlier.castSucc).castSucc =
              (Fin.cast (by simp) earlier.castSucc.castSucc :
                Fin ((priorEvents ++ [event]).length + 1)) := by
              ext
              rfl
          have outputEq : (Fin.cast (by simp) earlier.castSucc).succ =
              (Fin.cast (by simp) earlier.succ.castSucc :
                Fin ((priorEvents ++ [event]).length + 1)) := by
              ext
              rfl
          rw [inputEq, outputEq, nextGraphs_cast earlier.castSucc,
            nextStates_cast earlier.castSucc, nextChoices_cast earlier,
            nextStates_cast earlier.succ, nextGraphs_cast earlier.succ]
          simpa using transitions earlier

end Grass.RelationalSystem
