import Grass.Build.Cache.Key

/-!
# Measured shard and aggregate manifests

Leaf manifests retain exact cache environments and measured output data.
Aggregate manifests retain only direct child summaries and carry a checked
fanout bound. Composition meaning is supplied as an external relation.
-/

namespace Grass.Build.Manifest

open Grass.Build.Cache Grass.Specification Grass.Std.Logical

/-- Recorded build costs and artifact sizes for one manifest node. These are
observations in explicit units, not asymptotic or constant-time claims. -/
structure BuildMeasurement where
  elapsedNanoseconds : Nat
  peakResidentBytes : Nat
  oleanBytes : Nat
  proofBytes : Nat
  artifactBytes : Nat
  deriving DecidableEq, Repr

/-- The semantic-environment component responsible for an incremental rebuild. -/
inductive RebuildCause where
  | source
  | importedSummary
  | semanticProfile
  | verifier
  | toolchain
  | generator
  | options
  | auditPolicy
  deriving DecidableEq, Repr

/-- Whether a node was absent, replayed, or rebuilt. The
`BuildDisposition.rebuilt` constructor carries a proof that its named semantic
cause vector has nonzero length. -/
inductive BuildDisposition where
  | coldBuild
  | cacheHit
  | rebuilt (causes : Vec RebuildCause) (nonempty : causes.length ≠ 0)

/-- The compact information an aggregate retains for one direct child. It does
not contain the child's source, proof, artifact bytes, or descendant list. -/
structure ChildSummary where
  scope : ScopeId
  manifestRoot : Digest
  publicSummary : Digest
  deriving DecidableEq, Repr

/-- A leaf records its nominal scope, exact keyed semantic environment, compact
manifest/public/artifact digests, reported costs, and build disposition. -/
structure LeafManifest (hasher : MerkleHasher) where
  scope : ScopeId
  cache : CacheRecord hasher
  manifestRoot : Digest
  publicSummary : Digest
  artifact : Digest
  measurement : BuildMeasurement
  disposition : BuildDisposition

/-- One bounded-fanout aggregate node over direct child summaries. `fanout` is a
type index, so every consumer receives the bound proof with the value. -/
structure AggregateManifest (fanout : Nat) where
  scope : ScopeId
  children : Vec ChildSummary
  nonempty : children.length ≠ 0
  bounded : children.length ≤ fanout
  manifestRoot : Digest
  publicSummary : Digest
  measurement : BuildMeasurement

/-- Proof-erased value of a build disposition, retaining every semantic cause. -/
inductive BuildDispositionIdentity where
  | coldBuild
  | cacheHit
  | rebuilt (causes : Vec RebuildCause)
  deriving DecidableEq, Repr

/-- Erase only the nonempty proof from a disposition. -/
def BuildDisposition.identity : BuildDisposition → BuildDispositionIdentity
  | .coldBuild => .coldBuild
  | .cacheHit => .cacheHit
  | .rebuilt causes _ => .rebuilt causes

/-- Exact proof-free content identity of a leaf manifest. Unlike a digest, this
retains the semantic environment and every observable manifest field. -/
structure LeafManifestIdentity where
  scope : ScopeId
  environment : SemanticEnvironment
  cacheKey : Digest
  manifestRoot : Digest
  publicSummary : Digest
  artifact : Digest
  measurement : BuildMeasurement
  disposition : BuildDispositionIdentity
  deriving DecidableEq, Repr

/-- Exact proof-free content identity of an aggregate manifest. -/
structure AggregateManifestIdentity where
  scope : ScopeId
  children : Vec ChildSummary
  manifestRoot : Digest
  publicSummary : Digest
  measurement : BuildMeasurement
  deriving DecidableEq, Repr

/-- Exact proof-free identity of either concrete manifest kind. Constructors
preserve the leaf/aggregate distinction as well as all retained content. -/
inductive ManifestIdentity where
  | leaf (identity : LeafManifestIdentity)
  | aggregate (identity : AggregateManifestIdentity)
  deriving DecidableEq, Repr

/-- Nominal scope retained by either exact manifest identity. -/
def ManifestIdentity.scope : ManifestIdentity → ScopeId
  | .leaf identity => identity.scope
  | .aggregate identity => identity.scope

/-- Exact proof-free identity exported by a concrete leaf manifest. -/
def LeafManifest.identity {hasher : MerkleHasher}
    (manifest : LeafManifest hasher) : ManifestIdentity :=
  .leaf {
    scope := manifest.scope
    environment := manifest.cache.environment
    cacheKey := manifest.cache.key
    manifestRoot := manifest.manifestRoot
    publicSummary := manifest.publicSummary
    artifact := manifest.artifact
    measurement := manifest.measurement
    disposition := manifest.disposition.identity }

/-- Exact proof-free identity exported by a concrete aggregate manifest. -/
def AggregateManifest.identity {fanout : Nat}
    (manifest : AggregateManifest fanout) : ManifestIdentity :=
  .aggregate {
    scope := manifest.scope
    children := manifest.children
    manifestRoot := manifest.manifestRoot
    publicSummary := manifest.publicSummary
    measurement := manifest.measurement }

/-- Compact exported identity consumed by a concrete parent. -/
def LeafManifest.childSummary {hasher : MerkleHasher}
    (manifest : LeafManifest hasher) : ChildSummary where
  scope := manifest.scope
  manifestRoot := manifest.manifestRoot
  publicSummary := manifest.publicSummary

/-- Compact exported identity consumed by a concrete parent. -/
def AggregateManifest.childSummary {fanout : Nat}
    (manifest : AggregateManifest fanout) : ChildSummary where
  scope := manifest.scope
  manifestRoot := manifest.manifestRoot
  publicSummary := manifest.publicSummary

/-- A hierarchical certificate carries the aggregate result and a proof of the
caller-supplied composition relation over this node's direct children. The
relation remains owned by the verification layer that instantiates it. -/
structure AggregateCertificate {fanout : Nat} (manifest : AggregateManifest fanout)
    (Summary : Type) (Composes : Vec ChildSummary → Summary → Prop) where
  summary : Summary
  composition : Composes manifest.children summary

/-- The fanout bound exported by every aggregate manifest. -/
theorem AggregateManifest.children_bounded {fanout : Nat}
    (manifest : AggregateManifest fanout) :
    manifest.children.length ≤ fanout :=
  manifest.bounded

/-- Aggregate manifests always name at least one direct child. -/
theorem AggregateManifest.has_child {fanout : Nat}
    (manifest : AggregateManifest fanout) :
    ∃ child, child ∈ manifest.children := by
  have positive : 0 < manifest.children.length :=
    Nat.pos_of_ne_zero manifest.nonempty
  let child := manifest.children.get 0 positive
  refine ⟨child, Vec.mem_iff_exists_get?.2 ?_⟩
  exact ⟨0, Vec.get?_eq_some_get manifest.children 0 positive⟩

end Grass.Build.Manifest
