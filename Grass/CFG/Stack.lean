import Grass.Core.Identifiers

/-!
# Abstract stack shapes

This module records only construction-level facts: net stack depth and the
lexical stack scopes that are still open.  It does not encode an ABI, choose a
prologue, or claim that a machine instruction implements a stack effect.
-/

namespace Grass.CFG

/-- Stable identity of one lexical stack allocation scope. -/
structure StackScopeId where
  id : StableId
deriving Repr, DecidableEq, Hashable

/-- Stack shape at one CFG boundary.

`depth` is the number of bytes reserved relative to the routine's selected
origin.  The head of `openScopes` is the innermost live lexical scope.
-/
structure StackShape where
  depth : Nat
  openScopes : List StackScopeId
deriving Repr, DecidableEq

namespace StackShape

/-- The empty shape at a selected routine origin. -/
def empty : StackShape := ⟨0, []⟩

/-- Structural validity rejects reopening one lexical scope identity. -/
def wellFormed (shape : StackShape) : Bool :=
  decide shape.openScopes.Nodup

/-- Certificate-facing statement for `StackShape.wellFormed`. -/
def WellFormed (shape : StackShape) : Prop := shape.wellFormed = true

instance (shape : StackShape) : Decidable shape.WellFormed :=
  inferInstanceAs (Decidable (shape.wellFormed = true))

@[simp] theorem wellFormed_iff (shape : StackShape) :
    shape.WellFormed ↔ shape.openScopes.Nodup := by
  simp [WellFormed, wellFormed]

/-- Enter a fresh lexical stack scope. -/
def enterScope? (shape : StackShape) (scope : StackScopeId) : Option StackShape :=
  if shape.openScopes.contains scope then
    none
  else
    some { shape with openScopes := scope :: shape.openScopes }

/-- Leave exactly the innermost lexical stack scope. -/
def leaveScope? (shape : StackShape) (scope : StackScopeId) : Option StackShape :=
  match shape.openScopes with
  | current :: outer =>
      if current == scope then some { shape with openScopes := outer } else none
  | [] => none

/-- Entering a fresh scope and immediately leaving that same innermost scope
returns the original shape. -/
theorem leaveScope?_enterScope? (shape entered : StackShape) (scope : StackScopeId)
    (h : shape.enterScope? scope = some entered) :
    entered.leaveScope? scope = some shape := by
  simp only [enterScope?] at h
  split at h
  · contradiction
  · cases h
    simp [leaveScope?]

/-- `StackShape.enterScope?_wellFormed` preserves structural validity when the
entered identity is fresh. -/
theorem enterScope?_wellFormed (shape entered : StackShape) (scope : StackScopeId)
    (closed : shape.WellFormed)
    (h : shape.enterScope? scope = some entered) : entered.WellFormed := by
  rw [wellFormed_iff] at closed ⊢
  simp only [enterScope?] at h
  split at h
  · contradiction
  · cases h
    simp_all

/-- `StackShape.leaveScope?_wellFormed` preserves structural validity when the
requested identity is the innermost open scope. -/
theorem leaveScope?_wellFormed (shape left : StackShape) (scope : StackScopeId)
    (closed : shape.WellFormed)
    (h : shape.leaveScope? scope = some left) : left.WellFormed := by
  rw [wellFormed_iff] at closed ⊢
  simp only [leaveScope?] at h
  cases scopes : shape.openScopes with
  | nil => simp [scopes] at h
  | cons current outer =>
      simp only [scopes] at closed h
      split at h
      · cases h
        exact closed.tail
      · contradiction

end StackShape

/-- An explicit stack-depth transformation.  `release` is checked before
`reserve`, so an underflow is rejected rather than truncated by `Nat` subtraction. -/
structure StackDelta where
  release : Nat
  reserve : Nat
deriving Repr, DecidableEq

namespace StackDelta

/-- Apply a depth transformation without changing lexical-scope identity. -/
def apply? (delta : StackDelta) (shape : StackShape) : Option StackShape :=
  if delta.release ≤ shape.depth then
    some { shape with depth := shape.depth - delta.release + delta.reserve }
  else
    none

/-- A depth transformation is rejected exactly on stack underflow. -/
@[simp] theorem apply?_eq_none (delta : StackDelta) (shape : StackShape) :
    delta.apply? shape = none ↔ shape.depth < delta.release := by
  simp [apply?, Nat.not_le]

theorem apply?_openScopes (delta : StackDelta) (before after : StackShape)
    (h : delta.apply? before = some after) :
    after.openScopes = before.openScopes := by
  simp only [apply?] at h
  split at h
  · cases h
    rfl
  · contradiction

theorem apply?_depth (delta : StackDelta) (before after : StackShape)
    (h : delta.apply? before = some after) :
    after.depth = before.depth - delta.release + delta.reserve := by
  simp only [apply?] at h
  split at h
  · cases h
    rfl
  · contradiction

/-- `StackDelta.apply?_wellFormed` preserves the lexical-scope validity of a
successful depth-only transformation. -/
theorem apply?_wellFormed (delta : StackDelta) (before after : StackShape)
    (closed : before.WellFormed)
    (h : delta.apply? before = some after) : after.WellFormed := by
  rw [StackShape.wellFormed_iff] at closed ⊢
  rw [apply?_openScopes delta before after h]
  exact closed

end StackDelta

/-- Required congruence class for a stack depth at a boundary such as a call. -/
structure StackAlignment where
  modulus : Nat
  remainder : Nat
deriving Repr, DecidableEq

namespace StackAlignment

/-- An alignment requirement is meaningful when its modulus is positive and
its canonical remainder is smaller than that modulus. -/
def wellFormed (requirement : StackAlignment) : Bool :=
  0 < requirement.modulus && requirement.remainder < requirement.modulus

/-- Whether a stack shape satisfies an alignment requirement. -/
def accepts (requirement : StackAlignment) (shape : StackShape) : Bool :=
  requirement.wellFormed && shape.depth % requirement.modulus == requirement.remainder

/-- A well-formed alignment requirement has a positive modulus and a canonical
remainder. -/
@[simp] theorem wellFormed_iff (requirement : StackAlignment) :
    requirement.wellFormed ↔
      0 < requirement.modulus ∧ requirement.remainder < requirement.modulus := by
  simp [wellFormed]

/-- Alignment acceptance exposes both validity of the requirement and the
exact depth congruence checked by `StackAlignment.accepts`. -/
@[simp] theorem accepts_iff (requirement : StackAlignment) (shape : StackShape) :
    requirement.accepts shape ↔
      0 < requirement.modulus ∧
      requirement.remainder < requirement.modulus ∧
      shape.depth % requirement.modulus = requirement.remainder := by
  simp [accepts, wellFormed, and_assoc]

/-- `StackAlignment.wellFormed_of_accepts` proves that an accepted stack shape
cannot witness a malformed alignment requirement. -/
theorem wellFormed_of_accepts (requirement : StackAlignment) (shape : StackShape)
    (h : requirement.accepts shape) : requirement.wellFormed := by
  have accepted := (accepts_iff requirement shape).mp h
  exact (wellFormed_iff requirement).mpr ⟨accepted.1, accepted.2.1⟩

/-- An accepted stack shape has the exact requested depth remainder. -/
theorem depth_mod_eq_of_accepts (requirement : StackAlignment) (shape : StackShape)
    (h : requirement.accepts shape) :
    shape.depth % requirement.modulus = requirement.remainder := by
  exact (accepts_iff requirement shape).mp h |>.2.2

end StackAlignment

/-- Exact shape compatibility at a CFG edge.  `StackShape.compatible_iff`
states that compatibility requires equality of both depth and open scopes. -/
def StackShape.compatible (actual expected : StackShape) : Bool :=
  decide (actual = expected)

@[simp] theorem StackShape.compatible_iff (actual expected : StackShape) :
    actual.compatible expected ↔ actual = expected := by
  simp [StackShape.compatible]

end Grass.CFG
