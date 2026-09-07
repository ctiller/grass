import Grass.Build.Manifest.Invalidation

/-!
# Bounded manifest dependency DAGs and rebuild cones

The graph here is build metadata, not a replacement for the verification
certificate interfaces in `Grass.Certificate`. Nodes name only direct dependency
scopes, and every node carries the same static fanout bound. A well-formed graph
is stored in child-before-parent order; this both excludes cycles and lets the
rebuild-cone scan stream through the graph without flattening descendants.
-/

namespace Grass.Build.Manifest

open Grass.Specification Grass.Std.Logical

/-- One compact dependency-graph node. The vector contains direct dependencies
only; source bodies, proof terms, and transitive descendants are deliberately
absent. -/
structure DependencyNode (fanout : Nat) where
  scope : ScopeId
  dependencies : Vec ScopeId
  bounded : dependencies.length ≤ fanout
  deriving Repr

/-- A manifest graph in child-before-parent traversal order. Structural
well-formedness is a separate proposition so untrusted generated metadata can
be checked before it is admitted. -/
structure ManifestDag (fanout : Nat) where
  nodes : Vec (DependencyNode fanout)
  deriving Repr

/-- Executable recursive graph validation. Every direct dependency must already
have been seen, and every scope must be introduced exactly once. Consequently
every edge points strictly backwards in traversal order. -/
def nodesWellFormed {fanout : Nat} :
    List ScopeId → List (DependencyNode fanout) → Bool
  | _, [] => true
  | seen, node :: rest =>
      decide (node.scope ∉ seen) &&
      node.dependencies.all (fun dependency => decide (dependency ∈ seen)) &&
      nodesWellFormed (seen ++ [node.scope]) rest

/-- The graph has unique scopes and all dependency edges point to earlier
nodes. This is the executable-order formulation of finite acyclicity. -/
def ManifestDag.WellFormed {fanout : Nat} (dag : ManifestDag fanout) : Prop :=
  nodesWellFormed [] dag.nodes.toList = true

instance ManifestDag.instDecidableWellFormed {fanout : Nat}
    (dag : ManifestDag fanout) : Decidable dag.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Generated graph metadata admitted only after the executable ordering,
uniqueness, and edge-closure check succeeds. This carries no verification-layer
claim; it certifies only the manifest graph shape. -/
structure CheckedManifestDag (fanout : Nat) where
  graph : ManifestDag fanout
  wellFormed : graph.WellFormed

/-- Validate untrusted generated graph metadata before rebuild-cone use. -/
def checkManifestDag {fanout : Nat} (dag : ManifestDag fanout) :
    Option (CheckedManifestDag fanout) :=
  if valid : dag.WellFormed then some ⟨dag, valid⟩ else none

/-- Admission succeeds exactly for a well-formed graph. -/
theorem checkManifestDag_isSome_iff {fanout : Nat} (dag : ManifestDag fanout) :
    (checkManifestDag dag).isSome = true ↔ dag.WellFormed := by
  simp [checkManifestDag]

/-- A compact graph node never exceeds its configured direct fanout. -/
theorem DependencyNode.dependencies_bounded {fanout : Nat}
    (node : DependencyNode fanout) : node.dependencies.length ≤ fanout :=
  node.bounded

/-- Whether a node belongs to the rebuild cone given the scopes already known
to be affected. A node is affected exactly when it changed locally or one of
its direct dependencies is already affected. -/
def nodeAffected (changed : ScopeId → Bool) (affected : Vec ScopeId)
    {fanout : Nat} (node : DependencyNode fanout) : Bool :=
  changed node.scope ||
    node.dependencies.any fun dependency => affected.contains dependency

/-- Extend a streamed rebuild cone by one topologically ready node. -/
def extendRebuildCone (changed : ScopeId → Bool) (affected : Vec ScopeId)
    {fanout : Nat} (node : DependencyNode fanout) : Vec ScopeId :=
  if nodeAffected changed affected node then affected.push node.scope else affected

/-- Stream the graph once in child-before-parent order. No descendant source or
flattened certificate value is materialized. -/
def rebuildCone {fanout : Nat} (dag : ManifestDag fanout)
    (changed : ScopeId → Bool) : Vec ScopeId :=
  dag.nodes.foldl (fun affected node => extendRebuildCone changed affected node)
    Vec.empty

/-- Rebuild-cone computation on admitted graph metadata. -/
def CheckedManifestDag.rebuildCone {fanout : Nat}
    (dag : CheckedManifestDag fanout) (changed : ScopeId → Bool) : Vec ScopeId :=
  Grass.Build.Manifest.rebuildCone dag.graph changed

/-- `mem_extendRebuildCone_iff` states the exact one-node rebuild decision: it
preserves every previously affected scope and adds precisely the current scope
when the current node is locally changed or has an affected direct dependency. -/
theorem mem_extendRebuildCone_iff (changed : ScopeId → Bool)
    (affected : Vec ScopeId) {fanout : Nat} (node : DependencyNode fanout)
    (scope : ScopeId) :
    scope ∈ extendRebuildCone changed affected node ↔
      scope ∈ affected ∨
        (scope = node.scope ∧ nodeAffected changed affected node = true) := by
  by_cases isAffected : nodeAffected changed affected node = true
  · simp [extendRebuildCone, isAffected]
  · have isFalse : nodeAffected changed affected node = false := by
      cases value : nodeAffected changed affected node
      · rfl
      · exact absurd value isAffected
    simp [extendRebuildCone, isFalse]

/-- Extending the cone never loses a previously affected scope. -/
theorem mem_extendRebuildCone_of_mem (changed : ScopeId → Bool)
    (affected : Vec ScopeId) {fanout : Nat} (node : DependencyNode fanout)
    {scope : ScopeId} (present : scope ∈ affected) :
    scope ∈ extendRebuildCone changed affected node :=
  (mem_extendRebuildCone_iff changed affected node scope).2 (Or.inl present)

/-- A locally changed node is added when it is visited. -/
theorem own_scope_mem_extendRebuildCone_of_changed (changed : ScopeId → Bool)
    (affected : Vec ScopeId) {fanout : Nat} (node : DependencyNode fanout)
    (locallyChanged : changed node.scope = true) :
    node.scope ∈ extendRebuildCone changed affected node := by
  apply (mem_extendRebuildCone_iff changed affected node node.scope).2
  right
  exact ⟨rfl, by simp [nodeAffected, locallyChanged]⟩

/-- An affected direct dependency adds its parent when the parent is visited. -/
theorem own_scope_mem_extendRebuildCone_of_dependency
    (changed : ScopeId → Bool) (affected : Vec ScopeId) {fanout : Nat}
    (node : DependencyNode fanout) (dependency : ScopeId)
    (direct : dependency ∈ node.dependencies)
    (dependencyAffected : dependency ∈ affected) :
    node.scope ∈ extendRebuildCone changed affected node := by
  apply (mem_extendRebuildCone_iff changed affected node node.scope).2
  right
  refine ⟨rfl, ?_⟩
  have contains : affected.contains dependency = true :=
    (Vec.contains_iff_mem affected dependency).2 dependencyAffected
  have anyAffected :
      node.dependencies.any (fun candidate => affected.contains candidate) = true :=
    (Vec.any_eq_true_iff _ _).2 ⟨dependency, direct, contains⟩
  simp [nodeAffected, anyAffected]

end Grass.Build.Manifest
