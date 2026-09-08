import Grass.Build.Manifest.Hierarchy
import Tests.Build.Manifest.Campaign
import Tests.Build.Manifest.Rooted

/-! # Exact manifest hierarchy fixtures -/

namespace Grass.Tests.Build.Manifest.Hierarchy

open Grass.Build.Cache Grass.Build.Manifest Grass.Specification Grass.Std.Logical
open Grass.Tests.Build.Manifest

def digest : Digest := ⟨Vec.empty⟩

def hasher : MerkleHasher where
  leaf _ := digest
  branch _ _ := digest

def environment : SemanticEnvironment where
  source := digest
  importedSummaries := Vec.empty
  semanticProfile := digest
  verifier := digest
  toolchain := digest
  generator := digest
  options := digest
  auditPolicy := digest

def cache : CacheRecord hasher where
  environment := environment
  key := digest
  keyExact := rfl

def measurement : BuildMeasurement where
  elapsedNanoseconds := 1
  peakResidentBytes := 2
  oleanBytes := 3
  proofBytes := 4
  artifactBytes := 5

def leaf (scope : ScopeId) : LeafManifest hasher where
  scope := scope
  cache := cache
  publicSummary := digest
  artifact := digest
  measurement := measurement
  disposition := .cacheHit

def child (scope : ScopeId) : ChildSummary where
  scope := scope
  manifestRoot := digest
  publicSummary := digest

def aggregate (scope : ScopeId) (children : Vec ChildSummary)
    (nonempty : children.length ≠ 0 := by decide)
    (bounded : children.length ≤ 2 := by decide) : AggregateManifest 2 where
  scope := scope
  children := children
  nonempty := nonempty
  bounded := bounded
  manifestRoot := digest
  measurement := measurement

def manifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf (leaf leafA)
  , .leaf (leaf leafB)
  , .aggregate (aggregate component (Vec.fromList [child leafA, child leafB]))
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

example : manifests.map ManifestNode.toDependencyNode = fixtureDag.nodes := by
  decide

example : (checkManifestHierarchy fixtureDag manifests).isSome = true := by
  decide

def wrongChildren : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf (leaf leafA)
  , .leaf (leaf leafB)
  , .aggregate (aggregate component (Vec.singleton (child leafA)))
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

example : checkManifestHierarchy fixtureDag wrongChildren = none := by decide

def reordered : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf (leaf leafB)
  , .leaf (leaf leafA)
  , .aggregate (aggregate component (Vec.fromList [child leafA, child leafB]))
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

example : checkManifestHierarchy fixtureDag reordered = none := by decide

example : checkManifestHierarchy disconnectedDag
    (Vec.fromList [.leaf (leaf leafA), .leaf (leaf leafB)]) = none := by decide

example :
    (checkHierarchyStructure fixtureDag manifests completeCampaign).isSome = true :=
  by decide

example :
    checkHierarchyStructure fixtureDag wrongChildren completeCampaign = none :=
  by decide

example :
    checkHierarchyStructure fixtureDag manifests incompleteCampaign = none :=
  by decide

example :
    checkHierarchyStructure fixtureDag manifests overRebuildCampaign = none :=
  by decide

end Grass.Tests.Build.Manifest.Hierarchy
