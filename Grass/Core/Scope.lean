/-!
# Nominal scopes

`ScopeId` is the dependency-minimal identity of a reviewed module or subsystem
namespace. It is a structural path, not a content digest and not a generative
execution identifier. Keeping it in Core lets specification requirements and
process registries share the name without importing either layer through the
other.
-/

namespace Grass

/-- A reviewed, structurally nested namespace identity. -/
structure ScopeId where
  /-- Path segments from the outermost scope to the innermost. -/
  path : List String
  deriving DecidableEq, Repr

namespace ScopeId

/-- The root scope. -/
def root : ScopeId := ⟨[]⟩

/-- The scope one level inside this one. -/
def child (scope : ScopeId) (segment : String) : ScopeId :=
  ⟨scope.path ++ [segment]⟩

/-- `outer` contains `inner` when its structural path is a prefix. -/
def Contains (outer inner : ScopeId) : Prop :=
  outer.path.isPrefixOf inner.path = true

@[simp] theorem contains_self (scope : ScopeId) : scope.Contains scope := by
  simp [Contains]

@[simp] theorem root_contains (scope : ScopeId) : root.Contains scope := rfl

@[simp] theorem contains_child (scope : ScopeId) (segment : String) :
    scope.Contains (scope.child segment) := by
  simp [Contains, child]

/-- Adding a path segment produces a scope distinct from its parent. -/
theorem child_ne (scope : ScopeId) (segment : String) :
    scope.child segment ≠ scope := by
  intro equal
  have lengths := congrArg (fun current => current.path.length) equal
  simp [child] at lengths

end ScopeId

end Grass
