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
  deriving DecidableEq, Repr

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
      decide node.dependencies.toList.Nodup &&
      node.dependencies.all (fun dependency => decide (dependency ∈ seen)) &&
      nodesWellFormed (seen ++ [node.scope]) rest

/-- Propositional meaning of the executable graph check: scopes are introduced
once, every dependency is already available, and the same property holds after
the current scope is added to the traversal prefix. -/
def NodesOrdered {fanout : Nat} :
    List ScopeId → List (DependencyNode fanout) → Prop
  | _, [] => True
  | seen, node :: rest =>
      node.scope ∉ seen ∧
      node.dependencies.toList.Nodup ∧
      (∀ dependency ∈ node.dependencies, dependency ∈ seen) ∧
      NodesOrdered (seen ++ [node.scope]) rest

/-- `nodesWellFormed_eq_true_iff` proves that executable graph admission checks
exactly the stated uniqueness and child-before-parent conditions. -/
theorem nodesWellFormed_eq_true_iff {fanout : Nat}
    (seen : List ScopeId) (nodes : List (DependencyNode fanout)) :
    nodesWellFormed seen nodes = true ↔ NodesOrdered seen nodes := by
  induction nodes generalizing seen with
  | nil => simp [nodesWellFormed, NodesOrdered]
  | cons node rest inductionHypothesis =>
      simp [nodesWellFormed, NodesOrdered, Vec.all_eq_true_iff,
        inductionHypothesis, and_assoc]

/-- The graph has unique scopes and dependency edges, and every edge points to
an earlier node. This is the executable-order formulation of finite acyclicity. -/
def ManifestDag.WellFormed {fanout : Nat} (dag : ManifestDag fanout) : Prop :=
  nodesWellFormed [] dag.nodes.toList = true

/-- Logical characterization of admitted manifest DAGs. -/
theorem ManifestDag.wellFormed_iff_nodesOrdered {fanout : Nat}
    (dag : ManifestDag fanout) :
    dag.WellFormed ↔ NodesOrdered [] dag.nodes.toList :=
  nodesWellFormed_eq_true_iff [] dag.nodes.toList

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

/-- A node is selected exactly for a local change or an already-selected direct
dependency; no digest match or transitive flattened input participates. -/
theorem nodeAffected_eq_true_iff (changed : ScopeId → Bool)
    (affected : Vec ScopeId) {fanout : Nat} (node : DependencyNode fanout) :
    nodeAffected changed affected node = true ↔
      changed node.scope = true ∨
        ∃ dependency ∈ node.dependencies, dependency ∈ affected := by
  simp [nodeAffected, Vec.any_eq_true_iff, Vec.contains_iff_mem]

/-- Extend a streamed rebuild cone by one topologically ready node. -/
def extendRebuildCone (changed : ScopeId → Bool) (affected : Vec ScopeId)
    {fanout : Nat} (node : DependencyNode fanout) : Vec ScopeId :=
  if nodeAffected changed affected node then affected.push node.scope else affected

/-- Stream a topologically ordered node list, retaining the accumulated cone
between steps. -/
def scanRebuildCone (changed : ScopeId → Bool) {fanout : Nat} :
    Vec ScopeId → List (DependencyNode fanout) → Vec ScopeId
  | affected, [] => affected
  | affected, node :: rest =>
      scanRebuildCone changed (extendRebuildCone changed affected node) rest

/-- Stream the graph once in child-before-parent order. No descendant source or
flattened certificate value is materialized. -/
def rebuildCone {fanout : Nat} (dag : ManifestDag fanout)
    (changed : ScopeId → Bool) : Vec ScopeId :=
  scanRebuildCone changed Vec.empty dag.nodes.toList

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

/-- Fully expanded semantic form of `mem_extendRebuildCone_iff`: one streamed
step retains its input and adds no scope except the visited node, which is added
exactly for a local change or an affected direct dependency. -/
theorem mem_extendRebuildCone_semantics_iff (changed : ScopeId → Bool)
    (affected : Vec ScopeId) {fanout : Nat} (node : DependencyNode fanout)
    (scope : ScopeId) :
    scope ∈ extendRebuildCone changed affected node ↔
      scope ∈ affected ∨
        (scope = node.scope ∧
          (changed node.scope = true ∨
            ∃ dependency ∈ node.dependencies, dependency ∈ affected)) := by
  rw [mem_extendRebuildCone_iff, nodeAffected_eq_true_iff]

/-- Scanning concatenated node lists is the same as carrying the first scan's
cone into the second scan. -/
theorem scanRebuildCone_append (changed : ScopeId → Bool)
    {fanout : Nat} (affected : Vec ScopeId)
    (priorNodes suffix : List (DependencyNode fanout)) :
    scanRebuildCone changed affected (priorNodes ++ suffix) =
      scanRebuildCone changed (scanRebuildCone changed affected priorNodes) suffix := by
  induction priorNodes generalizing affected with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      simp [scanRebuildCone, inductionHypothesis]

/-- A whole scan never drops a scope already present in its input cone. -/
theorem mem_scanRebuildCone_of_mem (changed : ScopeId → Bool)
    {fanout : Nat} (affected : Vec ScopeId)
    (nodes : List (DependencyNode fanout)) {scope : ScopeId}
    (present : scope ∈ affected) :
    scope ∈ scanRebuildCone changed affected nodes := by
  induction nodes generalizing affected with
  | nil => exact present
  | cons node rest inductionHypothesis =>
      apply inductionHypothesis
      exact (mem_extendRebuildCone_iff changed affected node scope).2 (Or.inl present)

/-- `mem_scanRebuildCone_scope` rules out invented scopes: every final cone
member was either in the input cone or is the scope of a visited graph node. -/
theorem mem_scanRebuildCone_scope (changed : ScopeId → Bool)
    {fanout : Nat} (affected : Vec ScopeId)
    (nodes : List (DependencyNode fanout)) {scope : ScopeId}
    (present : scope ∈ scanRebuildCone changed affected nodes) :
    scope ∈ affected ∨ ∃ node ∈ nodes, scope = node.scope := by
  induction nodes generalizing affected with
  | nil => exact Or.inl present
  | cons node rest inductionHypothesis =>
      rcases inductionHypothesis
          (extendRebuildCone changed affected node) present with retained | later
      · rcases (mem_extendRebuildCone_iff changed affected node scope).1 retained with
          prior | ⟨current, _⟩
        · exact Or.inl prior
        · exact Or.inr ⟨node, by simp, current⟩
      · rcases later with ⟨laterNode, inRest, equal⟩
        exact Or.inr ⟨laterNode, by simp [inRest], equal⟩

/-- A locally changed node occurring anywhere in a scan belongs to the final
cone, independently of the surrounding prefix and suffix. -/
theorem changed_scope_mem_scanRebuildCone (changed : ScopeId → Bool)
    {fanout : Nat} (affected : Vec ScopeId)
    (priorNodes suffix : List (DependencyNode fanout))
    (node : DependencyNode fanout)
    (locallyChanged : changed node.scope = true) :
    node.scope ∈ scanRebuildCone changed affected (priorNodes ++ node :: suffix) := by
  rw [scanRebuildCone_append]
  simp only [scanRebuildCone]
  apply mem_scanRebuildCone_of_mem
  exact (mem_extendRebuildCone_semantics_iff changed
    (scanRebuildCone changed affected priorNodes) node node.scope).2
      (Or.inr ⟨rfl, Or.inl locallyChanged⟩)

/-- `parent_scope_mem_scanRebuildCone_of_dependency` proves that if a direct
dependency is in the cone after the prior nodes, visiting its parent puts that
parent in the final cone and the suffix cannot remove it. -/
theorem parent_scope_mem_scanRebuildCone_of_dependency
    (changed : ScopeId → Bool) {fanout : Nat} (affected : Vec ScopeId)
    (priorNodes suffix : List (DependencyNode fanout))
    (node : DependencyNode fanout) (dependency : ScopeId)
    (direct : dependency ∈ node.dependencies)
    (dependencyAffected :
      dependency ∈ scanRebuildCone changed affected priorNodes) :
    node.scope ∈ scanRebuildCone changed affected (priorNodes ++ node :: suffix) := by
  rw [scanRebuildCone_append]
  simp only [scanRebuildCone]
  apply mem_scanRebuildCone_of_mem
  exact (mem_extendRebuildCone_semantics_iff changed
    (scanRebuildCone changed affected priorNodes) node node.scope).2
      (Or.inr ⟨rfl, Or.inr ⟨dependency, direct, dependencyAffected⟩⟩)

/-- With an empty initial cone and no locally changed scope,
`scanRebuildCone_no_changes` produces the empty cone. -/
theorem scanRebuildCone_no_changes (changed : ScopeId → Bool)
    (noneChanged : ∀ scope, changed scope = false)
    {fanout : Nat} (nodes : List (DependencyNode fanout)) :
    scanRebuildCone changed Vec.empty nodes = Vec.empty := by
  induction nodes with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      have unaffected :
          extendRebuildCone changed Vec.empty node = Vec.empty := by
        simp [extendRebuildCone, nodeAffected, noneChanged, Vec.any_eq_true_iff,
          Vec.contains_iff_mem]
      simpa [scanRebuildCone, unaffected] using inductionHypothesis

/-- A graph with no locally changed scope has an empty rebuild cone. -/
theorem rebuildCone_no_changes {fanout : Nat} (dag : ManifestDag fanout)
    (changed : ScopeId → Bool) (noneChanged : ∀ scope, changed scope = false) :
    rebuildCone dag changed = Vec.empty :=
  scanRebuildCone_no_changes changed noneChanged dag.nodes.toList

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
