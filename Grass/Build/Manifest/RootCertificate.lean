import Grass.Build.Manifest.CertificateHierarchy

/-!
# Root certificates for manifest hierarchies

`ManifestHierarchy.rootNode` selects the final node of the child-before-parent
ordering. Rooted admission supplies the nonemptiness proof, exact hierarchy
alignment identifies the same final DAG node, and `CertifiedManifestHierarchy`
supplies its externally owned certificate gate.
-/

namespace Grass.Build.Manifest

open Grass.Build.Cache Grass.Std.Logical

universe u

/-- Every concrete manifest hierarchy contains at least one node. -/
theorem ManifestHierarchy.manifestsNonempty
    {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) :
    hierarchy.manifests.length ≠ 0 := by
  have sameLength : hierarchy.manifests.length =
      hierarchy.dag.graph.nodes.length := by
    simpa using congrArg Vec.length hierarchy.nodesExact
  intro empty
  apply hierarchy.dag.nonempty
  rw [← sameLength]
  exact empty

/-- Index of the final root in the concrete child-before-parent ordering. -/
def ManifestHierarchy.rootIndex {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) : Nat :=
  hierarchy.manifests.length - 1

/-- The final concrete manifest node, which is total because rooted hierarchies
are nonempty. -/
def ManifestHierarchy.rootNode {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) : ManifestNode hasher fanout :=
  hierarchy.manifests.get hierarchy.rootIndex (by
    have nonempty := hierarchy.manifestsNonempty
    simp only [ManifestHierarchy.rootIndex]
    omega)

/-- `ManifestHierarchy.rootNode_mem` exposes the root as a concrete hierarchy
member without leaking the underlying `Vec` representation. -/
theorem ManifestHierarchy.rootNode_mem
    {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) :
    hierarchy.rootNode ∈ hierarchy.manifests := by
  apply Vec.mem_iff_exists_get?.2
  refine ⟨hierarchy.rootIndex, ?_⟩
  exact Vec.get?_eq_some_get _ _ _

/-- `ManifestHierarchy.rootNode_aligned` identifies the selected concrete root
with the final compact DAG node at the same index. -/
theorem ManifestHierarchy.rootNode_aligned
    {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) :
    hierarchy.dag.graph.nodes.get? hierarchy.rootIndex =
      some hierarchy.rootNode.toDependencyNode := by
  have inRange : hierarchy.rootIndex < hierarchy.manifests.length := by
    have nonempty := hierarchy.manifestsNonempty
    simp only [ManifestHierarchy.rootIndex]
    omega
  rw [← hierarchy.nodesExact]
  rw [Vec.get?_map, Vec.get?_eq_some_get _ _ inRange]
  rfl

/-- `CertifiedManifestHierarchy.rootCertificate` exposes the external gate for
the uniquely selected final hierarchy node. -/
theorem CertifiedManifestHierarchy.rootCertificate
    {hasher : MerkleHasher} {fanout : Nat}
    {hierarchy : ManifestHierarchy hasher fanout}
    {LeafCertificate : LeafManifest hasher → Type u}
    {Summary : Type} {Composes : Vec ChildSummary → Summary → Prop}
    (certificates : CertifiedManifestHierarchy hierarchy LeafCertificate
      Summary Composes) :
    hierarchy.rootNode.CertificateGate LeafCertificate Summary Composes :=
  certificates.certificateFor hierarchy.rootNode hierarchy.rootNode_mem

/-- `CertifiedManifestHierarchy.rootLeafCertificate` specializes the root gate
when the rooted hierarchy consists of a leaf root. -/
theorem CertifiedManifestHierarchy.rootLeafCertificate
    {hasher : MerkleHasher} {fanout : Nat}
    {hierarchy : ManifestHierarchy hasher fanout}
    {LeafCertificate : LeafManifest hasher → Type u}
    {Summary : Type} {Composes : Vec ChildSummary → Summary → Prop}
    (certificates : CertifiedManifestHierarchy hierarchy LeafCertificate
      Summary Composes)
    (manifest : LeafManifest hasher)
    (isLeaf : hierarchy.rootNode = .leaf manifest) :
    Nonempty (LeafCertificate manifest) := by
  have gate := certificates.rootCertificate
  rw [isLeaf] at gate
  exact gate

/-- `CertifiedManifestHierarchy.rootAggregateComposition` exposes the composed
summary witnessed by an aggregate root certificate. -/
theorem CertifiedManifestHierarchy.rootAggregateComposition
    {hasher : MerkleHasher} {fanout : Nat}
    {hierarchy : ManifestHierarchy hasher fanout}
    {LeafCertificate : LeafManifest hasher → Type u}
    {Summary : Type} {Composes : Vec ChildSummary → Summary → Prop}
    (certificates : CertifiedManifestHierarchy hierarchy LeafCertificate
      Summary Composes)
    (manifest : AggregateManifest fanout)
    (isAggregate : hierarchy.rootNode = .aggregate manifest) :
    ∃ summary, Composes manifest.children summary := by
  have gate := certificates.rootCertificate
  rw [isAggregate] at gate
  rcases gate with ⟨certificate⟩
  exact ⟨certificate.summary, certificate.composition⟩

end Grass.Build.Manifest
