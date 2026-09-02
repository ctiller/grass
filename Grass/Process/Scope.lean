/-!
# Nominal scopes

A `ScopeId` is the reviewed identity of the module that owns a family of keys.
`docs/PROCESS_SHARDING.md` §1 is explicit about what it must and must not be:

> `StableProcessSignatureId` is a reviewed nominal identity plus interface
> version. Content hashes are cache keys only.

So this is a path, compared structurally, and never a digest.

## Why it is its own module

`Grass/Process/Protocol/Registry.lean` needs it to say which fragment owns a
key, and `Grass/Process/Network/Boundary.lean` needs it to say which scope owns
a requirement. Those two have nothing else to do with each other, and
`docs/OLEAN_SHARDING.md` §2 forbids importing a module "merely to unfold it" or
to reach one declaration inside it. A boundary that imported the whole protocol
registry to obtain a path type would put every registry change in the rebuild
cone of every requirement change.
-/

namespace Grass.Process

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

Containment, not equality, is what an aggregate's uniqueness fold needs: two
fragments may share an ancestor scope and still own disjoint namespaces, while
two fragments where one contains the other do not.
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

end Grass.Process
