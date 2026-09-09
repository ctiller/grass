import Grass.Console.Behavior

/-! Aggregate byte accounting for the bounded console interaction. -/

namespace Grass.Console.Accounting

open Grass.Std.Logical
open Grass.Semantics
open Grass.RelationalSystem
open Grass.Console.Behavior

/-- The bytes committed by a state are determined only by its exact output cut. -/
def committed {payload : Vec Byte} : (system payload).State → Vec Byte
  | .pending cut => cut.emitted
  | .finished cut _ => cut.emitted

/-- One coherent finite suffix appends exactly its emitted-byte events. -/
def Accounts {payload : Vec Byte} (before after : (system payload).State) (events : List Event) : Prop :=
  committed after = committed before ++ emittedBytes events

private theorem steps_accounting_aux {payload : Vec Byte}
    {before after : (system payload).State} {beforeGraph afterGraph : Unit} {events : List Event}
    (steps : (system payload).Steps before beforeGraph events after afterGraph) :
    True ∧ Accounts before after events := by
  induction steps with
  | refl => exact ⟨trivial, by simp [Accounts, emittedBytes]⟩
  | @step events current currentGraph choice event next nextGraph prior transition ih =>
    rcases choice with ⟨cut, response⟩
    cases response with
    | advance after strict =>
      rcases (step_iff.mp transition) with ⟨origin, eventEq, nextEq⟩
      subst current
      subst event
      subst next
      refine ⟨trivial, ?_⟩
      unfold Accounts at ih ⊢
      simp only [committed] at ih
      change after.emitted = committed before ++ emittedBytes (events ++ [.emitted (cut.between after)])
      rw [← OutputCut.advance_exact cut after (Nat.le_of_lt strict), ih.2, emittedBytes_append]
      simp [committed, emittedBytes, Vec.append_assoc]
    | finish cause =>
      rcases (step_iff.mp transition) with ⟨origin, allowed, eventEq, nextEq⟩
      subst current
      subst event
      subst next
      refine ⟨trivial, ?_⟩
      unfold Accounts at ih ⊢
      simp only [committed] at ih
      change cut.emitted = committed before ++ emittedBytes (events ++ [.terminal cause])
      rw [ih.2, emittedBytes_append]
      simp [committed, emittedBytes]

/-- Every finite suffix accounts for all emitted bytes, using
`OutputCut.advance_exact` for each positive advance. -/
theorem steps_accounting {payload : Vec Byte}
    {before after : (system payload).State} {beforeGraph afterGraph : Unit} {events : List Event}
    (steps : (system payload).Steps before beforeGraph events after afterGraph) :
    Accounts before after events :=
  (steps_accounting_aux steps).2

/-- Every initialized finite history emits precisely the prefix at its final
cut. Terminal events add no bytes. -/
theorem history_accounting {payload : Vec Byte} (history : (system payload).History) :
    emittedBytes history.path.events = committed history.state := by
  have initial : history.initialState = .pending (OutputCut.zero payload) := history.validInitial
  have accounting := steps_accounting history.path.steps
  have initialCommitted : committed history.initialState = Vec.empty := by
    rw [initial]
    exact OutputCut.emitted_zero
  change committed history.state = committed history.initialState ++ emittedBytes history.path.events at accounting
  rw [initialCommitted, Vec.empty_append] at accounting
  exact accounting.symm

/-- Extract the final exact cut from an arbitrary interaction state. -/
theorem history_accounting_at_cut {payload : Vec Byte} (history : (system payload).History) :
    ∃ cut, (history.state = .pending cut ∨ ∃ cause, history.state = .finished cut cause) ∧
      emittedBytes history.path.events = cut.emitted := by
  have state_cut : ∀ state : State payload, ∃ cut,
      (state = .pending cut ∨ ∃ cause, state = .finished cut cause) ∧ committed state = cut.emitted := by
    intro state
    cases state with
    | pending cut => exact ⟨cut, Or.inl rfl, rfl⟩
    | finished cut cause => exact ⟨cut, Or.inr ⟨cause, rfl⟩, rfl⟩
  obtain ⟨cut, shape, committedEq⟩ := state_cut history.state
  exact ⟨cut, shape, (history_accounting history).trans committedEq⟩

/-- A well-founded relation admits no infinitely descending natural-indexed sequence. -/
private theorem no_infinite_descent {α : Type _} {relation : α → α → Prop}
    (wellFounded : WellFounded relation) (sequence : Nat → α)
    (descends : ∀ index, relation (sequence (index + 1)) (sequence index)) : False := by
  have never : ∀ value, Acc relation value → ∀ index, sequence index ≠ value := by
    intro value accessible
    induction accessible with
    | intro current _ ih =>
      intro index equal
      exact ih (sequence (index + 1)) (equal ▸ descends index) (index + 1) rfl
  exact never (sequence 0) (wellFounded.apply (sequence 0)) 0 rfl

/-- No infinite transition sequence exists: every actual transition lowers the
bounded residual-output rank. Permanent waiting remains a separate history form. -/
theorem no_infinite_continuation {payload : Vec Byte} {state : State payload} {graph : Unit}
    {priorEvents : List Event}
    (continuation : (system payload).InfiniteContinuation state graph priorEvents) : False :=
  no_infinite_descent Nat.lt_wfRel.wf (fun index => rank (continuation.stateAt index))
    (fun index => by
      change rank (continuation.stateAt (index + 1)) < rank (continuation.stateAt index)
      exact step_rank_decreases (continuation.step index))

end Grass.Console.Accounting
