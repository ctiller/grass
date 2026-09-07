import Grass.Core.Scope

/-!
# Specification scope compatibility

Decision 132 places the dependency-minimal `ScopeId` in `Grass.Core.Scope`.
The aliases in this module preserve the original neutral-layer import and
qualified names for process consumers while all identities are definitionally
the single Core type.
-/

namespace Grass.Specification

/-- Compatibility name for the Core-owned nominal scope identity. -/
abbrev ScopeId := Grass.ScopeId

namespace ScopeId

/-- Compatibility name for the Core-owned constructor. -/
abbrev mk : List String → ScopeId := Grass.ScopeId.mk

/-- Compatibility name for the Core-owned path projection. -/
abbrev path : ScopeId → List String := Grass.ScopeId.path

/-- Compatibility name for `Grass.ScopeId.root`. -/
abbrev root := Grass.ScopeId.root

/-- Compatibility forwarding definition for `Grass.ScopeId.child`. -/
def child (scope : ScopeId) (segment : String) : ScopeId :=
  Grass.ScopeId.child scope segment

/-- Compatibility forwarding definition for `Grass.ScopeId.Contains`. -/
def Contains (outer inner : ScopeId) : Prop :=
  Grass.ScopeId.Contains outer inner

@[simp] theorem contains_self (scope : ScopeId) : scope.Contains scope :=
  Grass.ScopeId.contains_self scope

@[simp] theorem root_contains (scope : ScopeId) : root.Contains scope :=
  Grass.ScopeId.root_contains scope

@[simp] theorem contains_child (scope : ScopeId) (segment : String) :
    scope.Contains (scope.child segment) :=
  Grass.ScopeId.contains_child scope segment

theorem Contains.trans {outer middle inner : ScopeId}
    (outerMiddle : outer.Contains middle)
    (middleInner : middle.Contains inner) : outer.Contains inner :=
  Grass.ScopeId.Contains.trans outerMiddle middleInner

theorem Contains.antisymm {left right : ScopeId}
    (leftRight : left.Contains right)
    (rightLeft : right.Contains left) : left = right :=
  Grass.ScopeId.Contains.antisymm leftRight rightLeft

theorem child_ne (scope : ScopeId) (segment : String) :
    scope.child segment ≠ scope :=
  Grass.ScopeId.child_ne scope segment

end ScopeId

end Grass.Specification
