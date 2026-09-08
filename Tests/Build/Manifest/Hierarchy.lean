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
  manifestRoot := digest
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
  publicSummary := digest
  measurement := measurement

def manifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf (leaf leafA)
  , .leaf (leaf leafB)
  , .aggregate (aggregate component (Vec.fromList [child leafA, child leafB]))
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

def differentDigest : Digest := ⟨Vec.singleton 1⟩

def changedEnvironment : SemanticEnvironment :=
  { environment with source := differentDigest }

def changedCache : CacheRecord hasher where
  environment := changedEnvironment
  key := digest
  keyExact := rfl

def changedCacheManifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf { leaf leafA with cache := changedCache }
  , .leaf (leaf leafB)
  , .aggregate (aggregate component (Vec.fromList [child leafA, child leafB]))
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

def changedPublicSummaryManifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf { leaf leafA with publicSummary := differentDigest }
  , .leaf (leaf leafB)
  , .aggregate (aggregate component (Vec.fromList [child leafA, child leafB]))
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

def changedArtifactManifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf { leaf leafA with artifact := differentDigest }
  , .leaf (leaf leafB)
  , .aggregate (aggregate component (Vec.fromList [child leafA, child leafB]))
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

def forgedChild : ChildSummary :=
  { child leafA with publicSummary := differentDigest }

def forgedChildManifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf (leaf leafA)
  , .leaf (leaf leafB)
  , .aggregate (aggregate component (Vec.fromList [forgedChild, child leafB]))
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

def changedAggregateRootManifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf (leaf leafA)
  , .leaf (leaf leafB)
  , .aggregate { aggregate component (Vec.fromList [child leafA, child leafB]) with
      manifestRoot := differentDigest }
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

def changedFinalRootManifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf (leaf leafA)
  , .leaf (leaf leafB)
  , .aggregate (aggregate component (Vec.fromList [child leafA, child leafB]))
  , .aggregate { aggregate product (Vec.singleton (child component)) with
      manifestRoot := differentDigest } ]

def changedAggregateMeasurementManifests : Vec (ManifestNode hasher 2) := Vec.fromList
  [ .leaf (leaf leafA)
  , .leaf (leaf leafB)
  , .aggregate { aggregate component (Vec.fromList [child leafA, child leafB]) with
      measurement := { measurement with elapsedNanoseconds := 99 } }
  , .aggregate (aggregate product (Vec.singleton (child component))) ]

example : manifests.map ManifestNode.toDependencyNode = fixtureDag.nodes := by
  decide

example : (checkManifestHierarchy fixtureDag manifests).isSome = true := by
  decide

example : changedCacheManifests.map ManifestNode.toDependencyNode = fixtureDag.nodes :=
  by decide
example : ConcreteChildrenExact changedCacheManifests := by decide
example : ¬completeCampaign.ObservesManifests changedCacheManifests := by decide
example : checkHierarchyStructure fixtureDag changedCacheManifests completeCampaign = none :=
  by decide

example : changedPublicSummaryManifests.map ManifestNode.toDependencyNode =
    fixtureDag.nodes := by decide
example : ¬ConcreteChildrenExact changedPublicSummaryManifests := by decide
example : checkHierarchyStructure fixtureDag changedPublicSummaryManifests
    completeCampaign = none := by decide

example : changedArtifactManifests.map ManifestNode.toDependencyNode = fixtureDag.nodes :=
  by decide
example : ConcreteChildrenExact changedArtifactManifests := by decide
example : ¬completeCampaign.ObservesManifests changedArtifactManifests := by decide
example : checkHierarchyStructure fixtureDag changedArtifactManifests completeCampaign = none :=
  by decide

example : forgedChildManifests.map ManifestNode.toDependencyNode = fixtureDag.nodes :=
  by decide
example : ¬ConcreteChildrenExact forgedChildManifests := by decide
example : checkManifestHierarchy fixtureDag forgedChildManifests = none := by decide

example : changedAggregateRootManifests.map ManifestNode.toDependencyNode =
    fixtureDag.nodes := by decide
example : ¬ConcreteChildrenExact changedAggregateRootManifests := by decide
example : checkHierarchyStructure fixtureDag changedAggregateRootManifests
    completeCampaign = none := by decide

example : ConcreteChildrenExact changedFinalRootManifests := by decide
example : (checkManifestHierarchy fixtureDag changedFinalRootManifests).isSome = true :=
  by decide
example : ¬completeCampaign.ObservesManifests changedFinalRootManifests := by decide
example : checkHierarchyStructure fixtureDag changedFinalRootManifests
    completeCampaign = none := by decide

example : ConcreteChildrenExact changedAggregateMeasurementManifests := by decide
example : ¬completeCampaign.ObservesManifests
    changedAggregateMeasurementManifests := by decide
example : checkHierarchyStructure fixtureDag changedAggregateMeasurementManifests
    completeCampaign = none := by decide

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
