/-!
# Nominal scopes

A `ScopeId` is the reviewed identity of the module or subsystem that owns a
family of names. `docs/PROCESS_SHARDING.md` §1 is explicit about what it must
and must not be:

> `StableProcessSignatureId` is a reviewed nominal identity plus interface
> version. Content hashes are cache keys only.

So this is a path, compared structurally, and never a digest.

## Why it is in the neutral layer

Two unrelated things need it. A requirement key names the scope that owns a
platform requirement (`Grass/Specification/Boundary.lean`); a protocol registry
fragment names the scope that owns a family of process keys
(`Grass/Process/Protocol/Registry.lean`). Those have nothing else in common, and
`docs/OLEAN_SHARDING.md` §2 forbids importing a module to reach one declaration
inside it — a boundary that imported the whole protocol registry for a path type
would put every registry change in the rebuild cone of every requirement change.

It sits in `Grass.Specification` rather than in `Grass.Process` because
`agent-bus` disposition `coord1:5` puts the neutral vocabulary below both
`Grass.Semantics` and `Grass.Process`, and a scope identity is used on both
sides of that diamond.

## Provisional placement

`docs/MODULES.md` gives identifiers to `Grass.Core`, and this may belong there
once that layer has an owner and a `Uid` discipline to relate it to. It is here
rather than there because `Grass.Core` is currently `c-mem`'s temporary custody
and this plan does not intend to grow it. The decision is cheap to revisit: the
type has no dependencies and one field.
-/

namespace Grass.Specification

/--
The identity of a scope: the module or subsystem that owns a family of names.

Path segments rather than one string, because scopes nest and a merge has to
compare them structurally rather than by prefix matching on text.
-/
structure ScopeId where
  /-- The scope path, outermost first. -/
  path : List String
  deriving DecidableEq, Repr

namespace ScopeId

/-- The root scope. -/
def root : ScopeId := ⟨[]⟩

/-- The scope one level inside this one. -/
def child (scope : ScopeId) (segment : String) : ScopeId :=
  ⟨scope.path ++ [segment]⟩

/--
`outer` contains `inner`: every segment of `outer` is a prefix of `inner`'s.

Containment, not equality, is what an aggregate's namespace-uniqueness fold
needs: two fragments may share an ancestor scope and still own disjoint
namespaces, while two fragments where one contains the other do not.
-/
def Contains (outer inner : ScopeId) : Prop :=
  outer.path.isPrefixOf inner.path = true

@[simp] theorem contains_self (scope : ScopeId) : scope.Contains scope := by
  simp [Contains]

@[simp] theorem root_contains (scope : ScopeId) : root.Contains scope := rfl

@[simp] theorem contains_child (scope : ScopeId) (segment : String) :
    scope.Contains (scope.child segment) := by
  simp [Contains, child]

/-- A child scope is not its parent: adding a segment changes the path. -/
theorem child_ne (scope : ScopeId) (segment : String) :
    scope.child segment ≠ scope := by
  intro equal
  have lengths := congrArg (fun s => s.path.length) equal
  simp [child] at lengths

end ScopeId

end Grass.Specification
