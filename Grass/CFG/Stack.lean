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

end StackAlignment

/-- `StackShape.compatible` requires exact shape equality at a CFG edge,
including the live lexical stack-scope list rather than depth alone. -/
def StackShape.compatible (actual expected : StackShape) : Bool :=
  decide (actual = expected)

@[simp] theorem StackShape.compatible_iff (actual expected : StackShape) :
    actual.compatible expected ↔ actual = expected := by
  simp [StackShape.compatible]

end Grass.CFG
