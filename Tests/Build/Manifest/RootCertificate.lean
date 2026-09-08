import Grass.Build.Manifest.RootCertificate
import Tests.Build.Manifest.CertificateHierarchy

/-! # Root manifest-certificate fixtures -/

namespace Grass.Tests.Build.Manifest.RootCertificate

open Grass.Build.Manifest Grass.Std.Logical
open Grass.Tests.Build.Manifest.CertificateHierarchy
open Grass.Tests.Build.Manifest.Hierarchy

example : hierarchy.rootIndex = 3 := by decide

example : hierarchy.rootNode.scope = product := by decide

example : hierarchy.dag.graph.nodes.get? hierarchy.rootIndex =
    some hierarchy.rootNode.toDependencyNode :=
  hierarchy.rootNode_aligned

example : hierarchy.rootNode.CertificateGate LeafCertificate Nat
    CountsChildren :=
  certificates.rootCertificate

end Grass.Tests.Build.Manifest.RootCertificate
