import Grass.Build.Manifest.Hierarchy

/-!
# Certificate gates over manifest hierarchies

`CertifiedManifestHierarchy` consumes an externally supplied leaf-certificate
family and aggregate composition relation. Build/Manifest neither defines nor
weakens those verification gates; it requires evidence at every concrete node
already aligned with the rooted manifest DAG.
-/

namespace Grass.Build.Manifest

open Grass.Build.Cache Grass.Std.Logical

universe u

/-- The external certificate obligation for one concrete manifest node. -/
def ManifestNode.CertificateGate {hasher : MerkleHasher} {fanout : Nat}
    (LeafCertificate : LeafManifest hasher → Type u)
    (Summary : Type) (Composes : Vec ChildSummary → Summary → Prop) :
    ManifestNode hasher fanout → Prop
  | .leaf manifest => Nonempty (LeafCertificate manifest)
  | .aggregate manifest =>
      Nonempty (AggregateCertificate manifest Summary Composes)

/-- A rooted aligned hierarchy with every external certificate gate inhabited. -/
structure CertifiedManifestHierarchy {hasher : MerkleHasher} {fanout : Nat}
    (hierarchy : ManifestHierarchy hasher fanout)
    (LeafCertificate : LeafManifest hasher → Type u)
    (Summary : Type) (Composes : Vec ChildSummary → Summary → Prop) where
  certified : ∀ node ∈ hierarchy.manifests,
    node.CertificateGate LeafCertificate Summary Composes

/-- `CertifiedManifestHierarchy.certificateFor` exposes a named node's gate. -/
theorem CertifiedManifestHierarchy.certificateFor
    {hasher : MerkleHasher} {fanout : Nat}
    {hierarchy : ManifestHierarchy hasher fanout}
    {LeafCertificate : LeafManifest hasher → Type u}
    {Summary : Type} {Composes : Vec ChildSummary → Summary → Prop}
    (certificates : CertifiedManifestHierarchy hierarchy LeafCertificate
      Summary Composes)
    (node : ManifestNode hasher fanout) (present : node ∈ hierarchy.manifests) :
    node.CertificateGate LeafCertificate Summary Composes :=
  certificates.certified node present

/-- A certified hierarchy still exposes its exact manifest-to-DAG alignment. -/
theorem CertifiedManifestHierarchy.nodesExact
    {hasher : MerkleHasher} {fanout : Nat}
    {hierarchy : ManifestHierarchy hasher fanout}
    {LeafCertificate : LeafManifest hasher → Type u}
    {Summary : Type} {Composes : Vec ChildSummary → Summary → Prop}
    (_certificates : CertifiedManifestHierarchy hierarchy LeafCertificate
      Summary Composes) :
    hierarchy.manifests.map ManifestNode.toDependencyNode =
      hierarchy.dag.graph.nodes :=
  hierarchy.nodesExact

end Grass.Build.Manifest
