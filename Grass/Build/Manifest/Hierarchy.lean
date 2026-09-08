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

/-- Exact proof-free identity of either concrete manifest node. -/
def ManifestNode.identity {hasher : MerkleHasher} {fanout : Nat} :
    ManifestNode hasher fanout → ManifestIdentity
  | .leaf manifest => manifest.identity
  | .aggregate manifest => manifest.identity

/-- Compact identity exported to a concrete parent. -/
def ManifestNode.childSummary {hasher : MerkleHasher} {fanout : Nat} :
    ManifestNode hasher fanout → ChildSummary
  | .leaf manifest => manifest.childSummary
  | .aggregate manifest => manifest.childSummary

/-- Exact child summaries directly consumed by a concrete node. -/
def ManifestNode.childSummaries {hasher : MerkleHasher} {fanout : Nat} :
    ManifestNode hasher fanout → Vec ChildSummary
  | .leaf _ => Vec.empty
  | .aggregate manifest => manifest.children

/-- Every child summary consumed by every node equals the compact export of a
concrete node in the same hierarchy. Exact manifest values remain retained
separately; digest equality is never used as proof of full manifest equality. -/
def ConcreteChildrenExact {hasher : MerkleHasher} {fanout : Nat}
    (nodes : Vec (ManifestNode hasher fanout)) : Prop :=
  nodes.all (fun node =>
    node.childSummaries.all (fun child =>
      nodes.any fun actual => decide (actual.childSummary = child))) = true

instance instDecidableConcreteChildrenExact {hasher : MerkleHasher}
    {fanout : Nat} (nodes : Vec (ManifestNode hasher fanout)) :
    Decidable (ConcreteChildrenExact nodes) := by
  unfold ConcreteChildrenExact
  infer_instance

/-- `concreteChildrenExact_iff` exposes the exact adjacency checked by
`ConcreteChildrenExact`: every retained child value equals one concrete node's
export, not merely a scope or digest lookup hit. -/
theorem concreteChildrenExact_iff {hasher : MerkleHasher} {fanout : Nat}
    (nodes : Vec (ManifestNode hasher fanout)) :
    ConcreteChildrenExact nodes ↔
      ∀ node ∈ nodes, ∀ child ∈ node.childSummaries,
        ∃ actual ∈ nodes, actual.childSummary = child := by
  simp [ConcreteChildrenExact, Vec.all_eq_true_iff, Vec.any_eq_true_iff]

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
  childrenExact : ConcreteChildrenExact manifests

/-- Validate rooted graph structure and exact concrete-manifest alignment. -/
def checkManifestHierarchy {hasher : MerkleHasher} {fanout : Nat}
    (dag : ManifestDag fanout) (manifests : Vec (ManifestNode hasher fanout)) :
    Option (ManifestHierarchy hasher fanout) :=
  if rooted : dag.Rooted then
    if nodesExact : manifests.map ManifestNode.toDependencyNode = dag.nodes then
      if childrenExact : ConcreteChildrenExact manifests then
        some ⟨⟨dag, rooted⟩, manifests, nodesExact, childrenExact⟩
      else none
    else none
  else none

/-- `checkManifestHierarchy_isSome_iff` exactly characterizes hierarchy admission. -/
theorem checkManifestHierarchy_isSome_iff {hasher : MerkleHasher} {fanout : Nat}
    (dag : ManifestDag fanout) (manifests : Vec (ManifestNode hasher fanout)) :
    (checkManifestHierarchy dag manifests).isSome = true ↔
      dag.Rooted ∧ manifests.map ManifestNode.toDependencyNode = dag.nodes ∧
        ConcreteChildrenExact manifests := by
  by_cases rooted : dag.Rooted
  · by_cases nodesExact :
      manifests.map ManifestNode.toDependencyNode = dag.nodes
    · by_cases childrenExact : ConcreteChildrenExact manifests
      · simp [checkManifestHierarchy, rooted, nodesExact, childrenExact]
      · simp [checkManifestHierarchy, rooted, nodesExact, childrenExact]
    · simp [checkManifestHierarchy, rooted, nodesExact]
  · simp [checkManifestHierarchy, rooted]

/-- Every admitted hierarchy exposes the exact compact-node correspondence. -/
theorem ManifestHierarchy.nodes_exact {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) :
    hierarchy.manifests.map ManifestNode.toDependencyNode =
      hierarchy.dag.graph.nodes :=
  hierarchy.nodesExact

/-- Every consumed child summary in an admitted hierarchy is backed by a
concrete child node's exact exported summary. -/
theorem ManifestHierarchy.children_exact {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) :
    ConcreteChildrenExact hierarchy.manifests :=
  hierarchy.childrenExact

/-- Every retained report names the exact proof-free content identities of the
concrete manifest vector, including the final root identity. -/
def StructuralCampaign.ObservesManifests {hasher : MerkleHasher} {fanout : Nat}
    (campaign : StructuralCampaign)
    (manifests : Vec (ManifestNode hasher fanout)) : Prop :=
  campaign.runs.all (fun run => decide
    (run.manifestIdentities = manifests.map ManifestNode.identity)) = true

instance StructuralCampaign.instDecidableObservesManifests
    {hasher : MerkleHasher} {fanout : Nat} (campaign : StructuralCampaign)
    (manifests : Vec (ManifestNode hasher fanout)) :
    Decidable (campaign.ObservesManifests manifests) := by
  unfold StructuralCampaign.ObservesManifests
  infer_instance

/-- Exact semantic form of report-to-manifest binding. -/
theorem StructuralCampaign.observesManifests_iff
    {hasher : MerkleHasher} {fanout : Nat} (campaign : StructuralCampaign)
    (manifests : Vec (ManifestNode hasher fanout)) :
    campaign.ObservesManifests manifests ↔
      ∀ run ∈ campaign.runs,
        run.manifestIdentities = manifests.map ManifestNode.identity := by
  simp [StructuralCampaign.ObservesManifests, Vec.all_eq_true_iff]

/-- A concrete rooted hierarchy paired with a complete structurally exact
caller-supplied campaign. This type makes no empirical-authenticity claim. -/
structure CheckedHierarchyStructure (hasher : MerkleHasher) (fanout : Nat) where
  hierarchy : ManifestHierarchy hasher fanout
  campaign : CheckedStructuralCampaign hierarchy.dag.graph
  observesManifests : campaign.campaign.ObservesManifests hierarchy.manifests

/-- Jointly admit concrete manifests, their rooted DAG, and structurally
consistent caller-supplied reports. -/
def checkHierarchyStructure {hasher : MerkleHasher} {fanout : Nat}
    (dag : ManifestDag fanout) (manifests : Vec (ManifestNode hasher fanout))
    (campaign : StructuralCampaign) :
    Option (CheckedHierarchyStructure hasher fanout) :=
  if rooted : dag.Rooted then
    if nodesExact : manifests.map ManifestNode.toDependencyNode = dag.nodes then
      if childrenExact : ConcreteChildrenExact manifests then
        if complete : campaign.Complete then
          if exact : campaign.ExactFor dag then
            if observes : campaign.ObservesManifests manifests then
              some {
                hierarchy := ⟨⟨dag, rooted⟩, manifests, nodesExact, childrenExact⟩
                campaign := ⟨campaign, complete, exact⟩
                observesManifests := observes }
            else none
          else none
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
        ConcreteChildrenExact manifests ∧ campaign.Complete ∧
        campaign.ExactFor dag ∧ campaign.ObservesManifests manifests := by
  by_cases rooted : dag.Rooted
  · by_cases nodesExact :
        manifests.map ManifestNode.toDependencyNode = dag.nodes
    · by_cases childrenExact : ConcreteChildrenExact manifests
      · by_cases complete : campaign.Complete
        · by_cases exact : campaign.ExactFor dag
          · by_cases observes : campaign.ObservesManifests manifests
            · simp [checkHierarchyStructure, rooted, nodesExact, childrenExact,
                complete, exact, observes]
            · simp [checkHierarchyStructure, rooted, nodesExact, childrenExact,
                complete, exact, observes]
          · simp [checkHierarchyStructure, rooted, nodesExact, childrenExact,
              complete, exact]
        · simp [checkHierarchyStructure, rooted, nodesExact, childrenExact,
            complete]
      · simp [checkHierarchyStructure, rooted, nodesExact, childrenExact]
    · simp [checkHierarchyStructure, rooted, nodesExact]
  · simp [checkHierarchyStructure, rooted]

end Grass.Build.Manifest
