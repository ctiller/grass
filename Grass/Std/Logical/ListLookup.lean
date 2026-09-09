import Init.Data.List.Find
import Init.Data.List.Pairwise

/-! Lookup completeness for lists whose projected keys are unique. -/
namespace Grass.Std.Logical

universe u v

theorem find?_key_of_mem {α : Type u} {κ : Type v} [DecidableEq κ]
    {key : α → κ} {values : List α} (unique : (values.map key).Nodup)
    {value : α} (member : value ∈ values) :
    values.find? (fun candidate => decide (key candidate = key value)) = some value := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · have different : key head ≠ key value := by
          intro same
          exact unique.1 (List.mem_map.mpr ⟨value, member, same.symm⟩)
        rw [List.find?_cons_of_neg (by simpa using different)]
        exact ih unique.2 member

end Grass.Std.Logical