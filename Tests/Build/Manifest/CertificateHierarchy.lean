import Grass.Build.Manifest.CertificateHierarchy
import Tests.Build.Manifest.Hierarchy

/-! # Manifest certificate-gate fixtures -/

namespace Grass.Tests.Build.Manifest.CertificateHierarchy

open Grass.Build.Manifest Grass.Std.Logical
open Grass.Tests.Build.Manifest
open Grass.Tests.Build.Manifest.Hierarchy

def hierarchy : ManifestHierarchy hasher 2 where
  dag := ⟨fixtureDag, by decide⟩
  manifests := manifests
  nodesExact := by decide
  childrenExact := by decide

def LeafCertificate (_ : LeafManifest hasher) := Unit

def CountsChildren (children : Vec ChildSummary) (summary : Nat) : Prop :=
  summary = children.length

theorem gateForNode (node : ManifestNode hasher 2) :
    node.CertificateGate LeafCertificate Nat CountsChildren := by
  cases node with
  | leaf => exact ⟨()⟩
  | aggregate manifest =>
      exact ⟨{
        summary := manifest.children.length
        composition := rfl }⟩

theorem certificates : CertifiedManifestHierarchy hierarchy LeafCertificate
    Nat CountsChildren where
  certified := by
    intro node _present
    exact gateForNode node

example (node : ManifestNode hasher 2) (present : node ∈ hierarchy.manifests) :
    node.CertificateGate LeafCertificate Nat CountsChildren :=
  certificates.certificateFor node present

example : hierarchy.manifests.map ManifestNode.toDependencyNode =
    hierarchy.dag.graph.nodes :=
  certificates.nodesExact

/-- An uninhabited leaf gate prevents certification of a hierarchy containing
a leaf, even though all manifest and DAG metadata is structurally valid. -/
def ImpossibleLeafCertificate (_ : LeafManifest hasher) := Empty

example : ¬Nonempty (CertifiedManifestHierarchy hierarchy
    ImpossibleLeafCertificate Nat CountsChildren) := by
  rintro ⟨candidate⟩
  have present : (.leaf (leaf leafA) : ManifestNode hasher 2) ∈
      hierarchy.manifests := by
    apply Vec.mem_iff_mem_toList.mpr
    exact List.mem_cons_self
  have gate := candidate.certificateFor (.leaf (leaf leafA)) present
  rcases gate with ⟨impossible⟩
  exact nomatch impossible

end Grass.Tests.Build.Manifest.CertificateHierarchy
