import Grass.Resource.Algebra

/-! Neutral resources captured by one logical console-line contract. -/

namespace Grass

open Resource

/-- The authored console resource value.  It has exactly one inhabitant and
therefore introduces no count, budget, handle, or lifecycle policy. -/
inductive ConsoleResourceModel where
  | singleLine
deriving DecidableEq

namespace ConsoleResourceModel

/-- Singleton elimination is the equality fact used by every neutral-algebra
law which would otherwise need a resource-specific policy. -/
private theorem eq_singleLine (value : ConsoleResourceModel) : value = .singleLine := by
  cases value
  rfl

/-- The neutral whole-resource algebra for one logical console line. -/
def algebra : ResourceAlgebra ConsoleResourceModel where
  compatible := fun _ _ => True
  combine := fun _ _ => .singleLine
  alternative := fun _ _ => .singleLine
  zero := .singleLine
  le := fun _ _ => True
  laws := by
    refine {
      compatibleComm := fun _ _ _ => trivial
      compatibleZero := fun _ => trivial
      combineComm := fun _ _ _ => rfl
      combineAssoc := fun _ _ _ _ _ _ _ => rfl
      combineZero := fun _ => rfl
      leRefl := fun _ => trivial
      leTrans := fun _ _ _ _ _ => trivial
      leAntisymm := fun a b _ _ => (eq_singleLine a).trans (eq_singleLine b).symm
      zeroLe := fun _ => trivial
      leCombine := fun _ _ _ => trivial
      combineMonotone := fun _ _ _ _ _ _ => trivial
      combineCancel := fun a b _ _ _ => by
        intro _
        exact (eq_singleLine a).trans (eq_singleLine b).symm
      combineEqLeft := fun _ b _ _ => eq_singleLine b
      alternativeComm := fun _ _ => rfl
      alternativeAssoc := fun _ _ _ => rfl
      alternativeZero := fun _ => rfl
      alternativeIdem := fun _ => rfl
      leAlternative := fun _ _ => trivial
      alternativeMonotone := fun _ _ _ _ => trivial
      alternativeLeCombine := fun _ _ _ => trivial }

instance : ResourceModel ConsoleResourceModel where
  algebra := algebra

end ConsoleResourceModel

/-- The selected resource context captured at contract construction.  `model`
and `resources` are type indices, so Lean rejects reuse under a distinct model
dictionary or resource value before any selected-axis field is read. This
console instance selects no axes. -/
structure ConsoleResourceSnapshot {R : Type} (model : ResourceModel R) (resources : R) where
  selectedAxes : List ResourceAxisName
  selectedAxes_empty : selectedAxes = []

/-- A console capability supplies the construction-time snapshot for the actual
resource value.  Consumers retain the returned value rather than querying this
class later. -/
class ConsoleWriteResources (R : Type) [model : ResourceModel R] where
  snapshot : (resources : R) → ConsoleResourceSnapshot model resources

namespace ConsoleWriteResources

/-- Capture the exact context once from the selected capability. -/
def captured {R : Type} [model : ResourceModel R] [ConsoleWriteResources R] (resources : R) :
    ConsoleResourceSnapshot model resources :=
  ConsoleWriteResources.snapshot resources

/-- The neutral console resource has the exact empty selected-axis map. -/
instance : ConsoleWriteResources ConsoleResourceModel where
  snapshot := fun _ => ⟨[], rfl⟩

theorem captured_axes_empty {R : Type} [model : ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : (captured resources).selectedAxes = [] :=
  (captured resources).selectedAxes_empty

end ConsoleWriteResources
end Grass
