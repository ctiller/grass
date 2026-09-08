import Grass.Build.Manifest.CertificateHierarchy
import Tests.Build.Manifest.Hierarchy

/-! # Exact manifest certificate-gate fixtures -/

namespace Grass.Tests.Build.Manifest.CertificateHierarchy

open Grass Grass.Build.Manifest Grass.Std.Logical
open Grass.Tests.Build.Manifest
open Grass.Tests.Build.Manifest.Hierarchy

def hierarchy : ManifestHierarchy hasher 2 where
  dag := ⟨fixtureDag, by decide⟩
  manifests := manifests
  nodesExact := by decide
  childrenExact := by decide

inductive NoDemand

def noDemands : DemandFamily where
  Key := NoDemand
  keys := []
  complete := fun key => nomatch key
  unique := by simp
  identity := fun key => nomatch key
  identityInjective := fun left => nomatch left
  kind := fun key => nomatch key
  statement := fun key => nomatch key

theorem noDemandEvidence : DemandCertificateFamily noDemands where
  discharge := fun key => nomatch key

/-- Even a shard with no additional demands carries the concrete
g-foundation certificate type indexed by its exact manifest identity; the old
`Unit` certificate-family and `True` composition parameters no longer exist. -/
def certificateForIdentity (identity : ManifestIdentity) :
    ManifestCertificate identity where
  demands := noDemands
  evidence := noDemandEvidence

def certificates : CertifiedManifestHierarchy hierarchy where
  certified := by
    intro node _present
    exact certificateForIdentity node.identity

example (node : ManifestNode hasher 2) (present : node ∈ hierarchy.manifests) :
    ManifestCertificate node.identity :=
  certificates.certificateFor node present

example : hierarchy.manifests.map ManifestNode.toDependencyNode =
    hierarchy.dag.graph.nodes :=
  certificates.nodesExact

def componentNode : ManifestNode hasher 2 :=
  .aggregate (aggregate component (Vec.fromList [child leafA, child leafB]))

theorem componentPresent : componentNode ∈ hierarchy.manifests := by
  apply Vec.mem_iff_mem_toList.mpr
  simp [hierarchy, manifests, componentNode]

example : componentNode ∈ hierarchy.manifests := componentPresent
example : child leafA ∈ componentNode.childSummaries := by decide

/-- Aggregate lookup returns the actual child node, its exact exported summary,
and the foundation certificate indexed by that child's full manifest identity. -/
example : ∃ actual ∈ hierarchy.manifests,
    actual.childSummary = child leafA ∧
      Nonempty (ManifestCertificate.{0} actual.identity) := by
  exact certificates.childCertificate componentNode componentPresent
    (child leafA) (by decide)

/-- A forged child summary cannot pass the hierarchy needed by the certificate
gate, even though its scope-only dependency DAG is unchanged. -/
example : checkManifestHierarchy fixtureDag forgedChildManifests = none := by decide

end Grass.Tests.Build.Manifest.CertificateHierarchy
