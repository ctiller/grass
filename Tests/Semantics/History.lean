import Grass.Semantics.History

/-! Identical observations must not collapse histories with distinct choices. -/
namespace Grass.Tests.Semantics.History

open RelationalSystem

private def system : RelationalSystem Unit where
  State := Unit
  Choice := Bool
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private def chosen (choice : Bool) : system.History :=
  (History.initial (system := system) (state := ()) (graph := ()) trivial).append
    (Path.snoc (system := system) .nil choice () () () trivial)

/-- The old API deliberately forgets choices even when they are different. -/
theorem erased_choices_equal (first second : Bool) :
    (chosen first).erase = (chosen second).erase := by
  apply ExecutionPrefix.ext <;> rfl

/-- The new history retains every selected choice, not just its existence. -/
theorem chosen_injective : Function.Injective chosen := by
  intro first second equal
  have choices := congrArg (fun history : system.History => history.path.choices) equal
  simp only [chosen, History.append, History.initial, Path.append, Path.choices,
    List.nil_append] at choices
  have equalLists : ([first] : List Bool) = [second] := choices
  exact (List.cons.inj equalLists).1

/-- Same events and endpoints do not identify different choices. -/
theorem choices_distinct : chosen false ≠ chosen true := by
  intro equal
  have impossible := chosen_injective equal
  cases impossible

/-- Restriction loses no suffix data, including the second choice. -/
theorem two_step_reconstruct (first second : Bool) (count : Nat) :
    let history := (chosen first).append
      (Path.snoc (system := system) .nil second () () () trivial)
    (history.restrict count).append (history.path.cut count).after = history := by
  exact History.restrict_append _ _

end Grass.Tests.Semantics.History
