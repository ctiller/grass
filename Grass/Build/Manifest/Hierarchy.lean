import Grass.Build.Manifest.Campaign
import Grass.Build.Manifest.Rooted

/-!
# Exact manifest hierarchy alignment

`ManifestHierarchy` connects each compact dependency-DAG node to the concrete
leaf or aggregate manifest at the same position. `ManifestNode.toDependencyNode`
forgets measurements and digests while retaining exactly the scope and direct
child scopes used by hierarchical composition.
-/

namespace Grass.Build.Manifest

open Grass.Build.Cache Grass.Std.Logical

/-- A concrete leaf or aggregate manifest occupying one hierarchy node. -/
inductive ManifestNode (hasher : MerkleHasher) (fanout : Nat) where
  | leaf (manifest : LeafManifest hasher)
  | aggregate (manifest : AggregateManifest fanout)

/-- Scope exported by either concrete manifest-node form. -/
def ManifestNode.scope {hasher : MerkleHasher} {fanout : Nat} :
    ManifestNode hasher fanout → Grass.Specification.ScopeId
  | .leaf manifest => manifest.scope
  | .aggregate manifest => manifest.scope

/-- Direct child scopes; leaves have none and aggregates retain source order. -/
def ManifestNode.dependencies {hasher : MerkleHasher} {fanout : Nat} :
    ManifestNode hasher fanout → Vec Grass.Specification.ScopeId
  | .leaf _ => Vec.empty
  | .aggregate manifest => manifest.children.map ChildSummary.scope

/-- Forget one concrete manifest node to its exact compact DAG representation. -/
def ManifestNode.toDependencyNode {hasher : MerkleHasher} {fanout : Nat}
    (node : ManifestNode hasher fanout) : DependencyNode fanout where
  scope := node.scope
  dependencies := node.dependencies
  bounded := by
    cases node with
    | leaf => simp [ManifestNode.dependencies]
    | aggregate manifest =>
        simpa [ManifestNode.dependencies] using manifest.bounded

/-- A rooted compact DAG exactly aligned with its concrete manifest nodes. -/
structure ManifestHierarchy (hasher : MerkleHasher) (fanout : Nat) where
  dag : RootedManifestDag fanout
  manifests : Vec (ManifestNode hasher fanout)
  nodesExact : manifests.map ManifestNode.toDependencyNode = dag.graph.nodes

/-- Validate rooted graph structure and exact concrete-manifest alignment. -/
def checkManifestHierarchy {hasher : MerkleHasher} {fanout : Nat}
    (dag : ManifestDag fanout) (manifests : Vec (ManifestNode hasher fanout)) :
    Option (ManifestHierarchy hasher fanout) :=
  if rooted : dag.Rooted then
    if nodesExact : manifests.map ManifestNode.toDependencyNode = dag.nodes then
      some ⟨⟨dag, rooted⟩, manifests, nodesExact⟩
    else none
  else none

/-- `checkManifestHierarchy_isSome_iff` exactly characterizes hierarchy admission. -/
theorem checkManifestHierarchy_isSome_iff {hasher : MerkleHasher} {fanout : Nat}
    (dag : ManifestDag fanout) (manifests : Vec (ManifestNode hasher fanout)) :
    (checkManifestHierarchy dag manifests).isSome = true ↔
      dag.Rooted ∧ manifests.map ManifestNode.toDependencyNode = dag.nodes := by
  by_cases rooted : dag.Rooted
  · by_cases nodesExact :
        manifests.map ManifestNode.toDependencyNode = dag.nodes
    · simp [checkManifestHierarchy, rooted, nodesExact]
    · simp [checkManifestHierarchy, rooted, nodesExact]
  · simp [checkManifestHierarchy, rooted]

/-- Every admitted hierarchy exposes the exact compact-node correspondence. -/
theorem ManifestHierarchy.nodes_exact {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) :
    hierarchy.manifests.map ManifestNode.toDependencyNode =
      hierarchy.dag.graph.nodes :=
  hierarchy.nodesExact

/-- A concrete rooted hierarchy paired with a complete structurally exact
caller-supplied campaign. This type makes no empirical-authenticity claim. -/
structure CheckedHierarchyStructure (hasher : MerkleHasher) (fanout : Nat) where
  hierarchy : ManifestHierarchy hasher fanout
  campaign : CheckedStructuralCampaign hierarchy.dag.graph

/-- Jointly admit concrete manifests, their rooted DAG, and structurally
consistent caller-supplied reports. -/
def checkHierarchyStructure {hasher : MerkleHasher} {fanout : Nat}
    (dag : ManifestDag fanout) (manifests : Vec (ManifestNode hasher fanout))
    (campaign : StructuralCampaign) :
    Option (CheckedHierarchyStructure hasher fanout) :=
  if rooted : dag.Rooted then
    if nodesExact : manifests.map ManifestNode.toDependencyNode = dag.nodes then
      if complete : campaign.Complete then
        if exact : campaign.ExactFor dag then
          some {
            hierarchy := ⟨⟨dag, rooted⟩, manifests, nodesExact⟩
            campaign := ⟨campaign, complete, exact⟩ }
        else none
      else none
    else none
  else none

/-- `checkHierarchyStructure_isSome_iff` characterizes full structural admission. -/
theorem checkHierarchyStructure_isSome_iff {hasher : MerkleHasher} {fanout : Nat}
    (dag : ManifestDag fanout) (manifests : Vec (ManifestNode hasher fanout))
    (campaign : StructuralCampaign) :
    (checkHierarchyStructure dag manifests campaign).isSome = true ↔
      dag.Rooted ∧ manifests.map ManifestNode.toDependencyNode = dag.nodes ∧
        campaign.Complete ∧ campaign.ExactFor dag := by
  by_cases rooted : dag.Rooted
  · by_cases nodesExact :
        manifests.map ManifestNode.toDependencyNode = dag.nodes
    · by_cases complete : campaign.Complete
      · by_cases exact : campaign.ExactFor dag
        · simp [checkHierarchyStructure, rooted, nodesExact, complete, exact]
        · simp [checkHierarchyStructure, rooted, nodesExact, complete, exact]
      · simp [checkHierarchyStructure, rooted, nodesExact, complete]
    · simp [checkHierarchyStructure, rooted, nodesExact]
  · simp [checkHierarchyStructure, rooted]

end Grass.Build.Manifest
