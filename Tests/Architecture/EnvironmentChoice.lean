/-!
Minimal environment-choice quantifier experiment. This is not a Hello model,
native correspondence, or proof about Grass.BehaviorCorrespondence. It isolates
the same-prefix outcome-coverage obligation without library dependencies.
-/

namespace EnvironmentChoiceExperiment

inductive Outcome where | unavailable | success
deriving DecidableEq

inductive Plan where | fixed (outcome : Outcome) | unresolved

def Allows : Plan → Outcome → Prop
  | .fixed chosen, outcome => outcome = chosen
  | .unresolved, _ => True

inductive Lower where
  | waiting (plan : Plan)
  | selected (outcome : Outcome)
  | done (outcome : Outcome)

inductive Upper where
  | writing
  | reporting (outcome : Outcome)
  | observed (outcome : Outcome)

inductive LowerStep : Lower → Lower → Prop where
  | choose (allowed : Allows plan outcome) :
      LowerStep (.waiting plan) (.selected outcome)
  | finish : LowerStep (.selected outcome) (.done outcome)

inductive UpperStep : Upper → Upper → Prop where
  | choose : UpperStep .writing (.reporting outcome)
  | finish : UpperStep (.reporting outcome) (.observed outcome)

def LowerCompletes : Lower → Outcome → Prop
  | .waiting plan, outcome => Allows plan outcome
  | .selected chosen, outcome => outcome = chosen
  | .done chosen, outcome => outcome = chosen

def UpperCompletes : Upper → Outcome → Prop
  | .writing, _ => True
  | .reporting chosen, outcome => outcome = chosen
  | .observed chosen, outcome => outcome = chosen

def BackCoverage (lower : Lower) (upper : Upper) : Prop :=
  ∀ outcome, UpperCompletes upper outcome → LowerCompletes lower outcome

/-- A union over environments can cover all outcomes. -/
theorem union_covers : ∀ outcome, ∃ plan,
    LowerCompletes (.waiting plan) outcome := by
  intro outcome
  exact ⟨.fixed outcome, rfl⟩

/-- That union does not establish coverage at the fixed absent-stdout prefix. -/
theorem fixed_unavailable_fails :
    ¬ BackCoverage (.waiting (.fixed .unavailable)) .writing := by
  intro covers
  have impossible := covers .success trivial
  cases impossible

/-- Committing invisibly while retaining the upper writing state also fails. -/
theorem selected_unavailable_fails :
    ¬ BackCoverage (.selected .unavailable) .writing := by
  intro covers
  have impossible := covers .success trivial
  cases impossible

/-- A usable-route commitment also fails if the upper frontier still admits
unavailability. Relational future choices must retain the entire reply set. -/
theorem fixed_success_fails :
    ¬ BackCoverage (.waiting (.fixed .success)) .writing := by
  intro covers
  have impossible := covers .unavailable trivial
  cases impossible

/-- After a final success commitment, a still-open upper frontier is too wide. -/
theorem selected_success_fails :
    ¬ BackCoverage (.selected .success) .writing := by
  intro covers
  have impossible := covers .unavailable trivial
  cases impossible

inductive Related : Lower → Upper → Prop where
  | initial : Related (.waiting .unresolved) .writing
  | selected : Related (.selected outcome) (.reporting outcome)
  | done : Related (.done outcome) (.observed outcome)

/-- Both sides commit the same choice at the matched transition. -/
theorem step_back (related : Related lower upper)
    (step : UpperStep upper nextUpper) :
    ∃ nextLower, LowerStep lower nextLower ∧ Related nextLower nextUpper := by
  cases related with
  | initial =>
      cases step with
      | choose => exact ⟨_, .choose trivial, .selected⟩
  | selected =>
      cases step with
      | finish => exact ⟨_, .finish, .done⟩
  | done => cases step

theorem step_forth (related : Related lower upper)
    (step : LowerStep lower nextLower) :
    ∃ nextUpper, UpperStep upper nextUpper ∧ Related nextLower nextUpper := by
  cases related with
  | initial =>
      cases step with
      | choose allowed => exact ⟨_, .choose, .selected⟩
  | selected =>
      cases step with
      | finish => exact ⟨_, .finish, .done⟩
  | done => cases step

/-- Coverage holds from every related prefix, including after commitment. -/
theorem every_related_prefix (related : Related lower upper) :
    BackCoverage lower upper := by
  cases related <;> intro outcome allowed <;> exact allowed

/-- Once selected, the remaining completion cannot revise the outcome. -/
theorem stable_after_choice
    (complete : LowerCompletes (.selected chosen) outcome) : outcome = chosen :=
  complete

end EnvironmentChoiceExperiment
