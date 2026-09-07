import Grass.Build.Manifest.Dag

/-! # Bounded dependency-DAG and rebuild-cone fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Manifest Grass.Specification Grass.Std.Logical

def leafA : ScopeId := ScopeId.root.child "a"
def leafB : ScopeId := ScopeId.root.child "b"
def component : ScopeId := ScopeId.root.child "component"
def product : ScopeId := ScopeId.root.child "product"

def node (scope : ScopeId) (dependencies : Vec ScopeId)
    (bounded : dependencies.length ≤ 2 := by decide) : DependencyNode 2 where
  scope := scope
  dependencies := dependencies
  bounded := bounded

def fixtureDag : ManifestDag 2 where
  nodes := Vec.fromList
    [ node leafA Vec.empty
    , node leafB Vec.empty
    , node component (Vec.fromList [leafA, leafB])
    , node product (Vec.singleton component) ]

example : fixtureDag.WellFormed := by decide

example : (checkManifestDag fixtureDag).isSome = true := by decide

def onlyAChanged (scope : ScopeId) : Bool := scope == leafA

/-- One changed leaf invalidates its ancestor path, while the sibling remains
reusable. -/
example : rebuildCone fixtureDag onlyAChanged =
    Vec.fromList [leafA, component, product] := by
  decide

def interfaceChanged (scope : ScopeId) : Bool := scope == component

/-- An interface edit starts at the owning aggregate and reaches its parent; it
does not rebuild either unchanged leaf. -/
example : rebuildCone fixtureDag interfaceChanged =
    Vec.fromList [component, product] := by
  decide

def nothingChanged (_ : ScopeId) : Bool := false

example : rebuildCone fixtureDag nothingChanged = Vec.empty := by
  decide

/-- The fanout index prevents constructing a two-dependency node at fanout one. -/
example : ¬∃ candidate : DependencyNode 1,
    candidate.dependencies = Vec.fromList [leafA, leafB] := by
  rintro ⟨candidate, equal⟩
  have bounded := candidate.dependencies_bounded
  rw [equal] at bounded
  simp [Vec.length] at bounded

/-- A forward edge is rejected: dependencies must have appeared earlier. -/
def forwardEdgeDag : ManifestDag 2 where
  nodes := Vec.fromList
    [ node component (Vec.singleton leafA)
    , node leafA Vec.empty ]

example : ¬forwardEdgeDag.WellFormed := by decide

example : checkManifestDag forwardEdgeDag = none := by decide

/-- Duplicate scope identities are rejected even if their dependency lists are
otherwise valid. -/
def duplicateDag : ManifestDag 2 where
  nodes := Vec.fromList [node leafA Vec.empty, node leafA Vec.empty]

example : ¬duplicateDag.WellFormed := by decide

def leftParent : ScopeId := ScopeId.root.child "left"
def rightParent : ScopeId := ScopeId.root.child "right"

/-- A shared leaf feeds two independent parents before their common root: this
is a DAG rather than a duplicated tree representation. -/
def diamondDag : ManifestDag 2 where
  nodes := Vec.fromList
    [ node leafA Vec.empty
    , node leftParent (Vec.singleton leafA)
    , node rightParent (Vec.singleton leafA)
    , node product (Vec.fromList [leftParent, rightParent]) ]

example : diamondDag.WellFormed := by decide

example : rebuildCone diamondDag onlyAChanged =
    Vec.fromList [leafA, leftParent, rightParent, product] := by
  decide

end Grass.Tests.Build.Manifest
