import Grass.Build.Manifest.Hierarchy
import Grass.Core.Demand

/-!
# Foundation certificate gates over manifest hierarchies

`CertifiedManifestHierarchy` consumes `DemandCertificateFamily`, the
g-foundation certificate gate, indexed by each exact manifest identity. It has
no caller-selected certificate type or composition relation. Concrete child
adjacency comes from `ManifestHierarchy.childrenExact`, so a parent certificate
can obtain the exact foundation certificate attached to every actual child.
-/

namespace Grass.Build.Manifest

open Grass Grass.Build.Cache Grass.Std.Logical

universe u

/-- A g-foundation demand certificate attached to one exact manifest identity.
The identity is a type index, so substituting any semantic environment,
artifact, summary, child vector, or root input changes the required certificate
type. Measurements and dispositions remain outside semantic identity. -/
structure ManifestCertificate (identity : ManifestIdentity) where
  demands : DemandFamily.{u}
  evidence : DemandCertificateFamily demands

/-- A rooted, exactly aligned hierarchy with a g-foundation demand certificate
for every concrete manifest node. -/
structure CertifiedManifestHierarchy {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout) where
  certified : ∀ node ∈ hierarchy.manifests, ManifestCertificate node.identity

/-- Obtain the exact identity-indexed foundation certificate for one concrete
node selected from the hierarchy. -/
def CertifiedManifestHierarchy.certificateFor
    {hasher : MerkleHasher} {fanout : Nat}
    {hierarchy : ManifestHierarchy hasher fanout}
    (certificates : CertifiedManifestHierarchy hierarchy)
    (node : ManifestNode hasher fanout) (present : node ∈ hierarchy.manifests) :
    ManifestCertificate.{0} node.identity :=
  certificates.certified node present

/-- Every direct child consumed by a concrete parent selects an actual child
node and its exact identity-indexed g-foundation certificate. -/
theorem CertifiedManifestHierarchy.childCertificate
    {hasher : MerkleHasher} {fanout : Nat}
    {hierarchy : ManifestHierarchy hasher fanout}
    (certificates : CertifiedManifestHierarchy hierarchy)
    (parent : ManifestNode hasher fanout) (parentPresent : parent ∈ hierarchy.manifests)
    (child : ChildSummary) (childPresent : child ∈ parent.childSummaries) :
    ∃ actual ∈ hierarchy.manifests,
      actual.childSummary = child ∧
        Nonempty (ManifestCertificate.{0} actual.identity) := by
  obtain ⟨actual, actualPresent, exactSummary⟩ :=
    (concreteChildrenExact_iff hierarchy.manifests).mp hierarchy.childrenExact
      parent parentPresent child childPresent
  exact ⟨actual, actualPresent, exactSummary,
    ⟨certificates.certificateFor actual actualPresent⟩⟩

/-- A certified hierarchy still exposes its exact manifest-to-DAG alignment. -/
theorem CertifiedManifestHierarchy.nodesExact
    {hasher : MerkleHasher} {fanout : Nat}
    {hierarchy : ManifestHierarchy hasher fanout}
    (_certificates : CertifiedManifestHierarchy hierarchy) :
    hierarchy.manifests.map ManifestNode.toDependencyNode =
      hierarchy.dag.graph.nodes :=
  hierarchy.nodesExact

end Grass.Build.Manifest
