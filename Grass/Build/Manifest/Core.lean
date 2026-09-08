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
  publicSummary : Digest
  artifact : Digest
  measurement : BuildMeasurement
  disposition : BuildDisposition

/-- One bounded-fanout aggregate node over direct child summaries. `fanout` is a
type index, so every consumer receives the bound proof with the value. -/
structure AggregateManifest (hasher : MerkleHasher) (fanout : Nat) where
  scope : ScopeId
  children : Vec ChildSummary
  nonempty : children.length ≠ 0
  bounded : children.length ≤ fanout
  publicSummary : Digest
  measurement : BuildMeasurement

/-- Canonical domain-separated leaf-manifest preimage. Measurement and build
disposition are excluded because they describe an observation, not semantic
manifest identity. -/
def LeafManifest.merkleTree {hasher : MerkleHasher}
    (manifest : LeafManifest hasher) : MerkleTree :=
  .branch (.leaf .leafManifestTag) <|
    .branch (.leaf (.manifestScope manifest.scope)) <|
      .branch manifest.cache.environment.merkleTree <|
        .branch (.leaf (.manifestPublicSummary manifest.publicSummary))
          (.leaf (.manifestArtifact manifest.artifact))

/-- Canonical leaf-manifest root. The exact preimage remains in the manifest;
this digest is a lookup and composition identity, not proof authority. -/
def LeafManifest.manifestRoot {hasher : MerkleHasher}
    (manifest : LeafManifest hasher) : Digest :=
  manifest.merkleTree.digest hasher

/-- Canonical ordered preimage for direct child summaries. -/
def childSummariesMerkleTree (children : Vec ChildSummary) : MerkleTree :=
  children.foldr
    (fun child rest =>
      .branch
        (.branch (.leaf (.manifestScope child.scope))
          (.branch (.leaf (.childManifestRoot child.manifestRoot))
            (.leaf (.childPublicSummary child.publicSummary))))
        rest)
    (.leaf .noMoreManifestChildren)

/-- Canonical domain-separated aggregate-manifest preimage. -/
def AggregateManifest.merkleTree {hasher : MerkleHasher} {fanout : Nat}
    (manifest : AggregateManifest hasher fanout) : MerkleTree :=
  .branch (.leaf .aggregateManifestTag) <|
    .branch (.leaf (.manifestScope manifest.scope)) <|
      .branch (childSummariesMerkleTree manifest.children)
        (.leaf (.manifestPublicSummary manifest.publicSummary))

/-- Canonical aggregate-manifest root, excluding reported measurement. -/
def AggregateManifest.manifestRoot {hasher : MerkleHasher} {fanout : Nat}
    (manifest : AggregateManifest hasher fanout) : Digest :=
  manifest.merkleTree.digest hasher

/-- `LeafManifest.manifestRoot_observation_irrelevant` proves reported costs and
disposition do not perturb semantic manifest identity. -/
@[simp] theorem LeafManifest.manifestRoot_observation_irrelevant
    {hasher : MerkleHasher} (manifest : LeafManifest hasher)
    (measurement : BuildMeasurement) (disposition : BuildDisposition) :
    LeafManifest.manifestRoot
        ({ manifest with measurement := measurement, disposition := disposition }) =
      manifest.manifestRoot := rfl

/-- `AggregateManifest.manifestRoot_observation_irrelevant` proves aggregate
reported costs do not perturb semantic manifest identity. -/
@[simp] theorem AggregateManifest.manifestRoot_observation_irrelevant
    {hasher : MerkleHasher} {fanout : Nat}
    (manifest : AggregateManifest hasher fanout)
    (measurement : BuildMeasurement) :
    AggregateManifest.manifestRoot (hasher := hasher)
        ({ manifest with measurement := measurement }) =
      manifest.manifestRoot := rfl

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

/-- Exact semantic identity of a leaf manifest. Unlike a digest, this retains
the semantic-environment preimage. Reported measurement and disposition are
excluded, matching `LeafManifest.merkleTree`. -/
structure LeafManifestIdentity where
  scope : ScopeId
  environment : SemanticEnvironment
  cacheKey : Digest
  manifestRoot : Digest
  publicSummary : Digest
  artifact : Digest
  deriving DecidableEq, Repr

/-- Exact proof-free content identity of an aggregate manifest. -/
structure AggregateManifestIdentity where
  scope : ScopeId
  children : Vec ChildSummary
  manifestRoot : Digest
  publicSummary : Digest
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

/-- Exact proof-free record of a leaf manifest, pairing semantic identity with
the build observation fields deliberately excluded from its root. -/
structure LeafManifestRecord where
  identity : LeafManifestIdentity
  measurement : BuildMeasurement
  disposition : BuildDispositionIdentity
  deriving DecidableEq, Repr

/-- Exact proof-free record of an aggregate manifest. -/
structure AggregateManifestRecord where
  identity : AggregateManifestIdentity
  measurement : BuildMeasurement
  deriving DecidableEq, Repr

/-- Full record identity used to bind reported observations to concrete
manifests without making those observations semantic cache inputs. -/
inductive ManifestRecordIdentity where
  | leaf (record : LeafManifestRecord)
  | aggregate (record : AggregateManifestRecord)
  deriving DecidableEq, Repr

/-- Nominal scope retained by either full manifest record. -/
def ManifestRecordIdentity.scope : ManifestRecordIdentity → ScopeId
  | .leaf record => record.identity.scope
  | .aggregate record => record.identity.scope

/-- Exact proof-free identity exported by a concrete leaf manifest. -/
def LeafManifest.identity {hasher : MerkleHasher}
    (manifest : LeafManifest hasher) : ManifestIdentity :=
  .leaf {
    scope := manifest.scope
    environment := manifest.cache.environment
    cacheKey := manifest.cache.key
    manifestRoot := manifest.manifestRoot
    publicSummary := manifest.publicSummary
    artifact := manifest.artifact }

/-- Exact proof-free identity exported by a concrete aggregate manifest. -/
def AggregateManifest.identity {hasher : MerkleHasher} {fanout : Nat}
    (manifest : AggregateManifest hasher fanout) : ManifestIdentity :=
  .aggregate {
    scope := manifest.scope
    children := manifest.children
    manifestRoot := manifest.manifestRoot
    publicSummary := manifest.publicSummary }

/-- Exact full record exported for structural observation binding. -/
def LeafManifest.recordIdentity {hasher : MerkleHasher}
    (manifest : LeafManifest hasher) : ManifestRecordIdentity :=
  .leaf {
    identity := {
      scope := manifest.scope
      environment := manifest.cache.environment
      cacheKey := manifest.cache.key
      manifestRoot := manifest.manifestRoot
      publicSummary := manifest.publicSummary
      artifact := manifest.artifact }
    measurement := manifest.measurement
    disposition := manifest.disposition.identity }

/-- Exact full record exported for structural observation binding. -/
def AggregateManifest.recordIdentity {hasher : MerkleHasher} {fanout : Nat}
    (manifest : AggregateManifest hasher fanout) : ManifestRecordIdentity :=
  .aggregate {
    identity := {
      scope := manifest.scope
      children := manifest.children
      manifestRoot := manifest.manifestRoot
      publicSummary := manifest.publicSummary }
    measurement := manifest.measurement }

/-- Compact exported identity consumed by a concrete parent. -/
def LeafManifest.childSummary {hasher : MerkleHasher}
    (manifest : LeafManifest hasher) : ChildSummary where
  scope := manifest.scope
  manifestRoot := manifest.manifestRoot
  publicSummary := manifest.publicSummary

/-- Compact exported identity consumed by a concrete parent. -/
def AggregateManifest.childSummary {hasher : MerkleHasher} {fanout : Nat}
    (manifest : AggregateManifest hasher fanout) : ChildSummary where
  scope := manifest.scope
  manifestRoot := manifest.manifestRoot
  publicSummary := manifest.publicSummary

/-- The fanout bound exported by every aggregate manifest. -/
theorem AggregateManifest.children_bounded {fanout : Nat}
    {hasher : MerkleHasher} (manifest : AggregateManifest hasher fanout) :
    manifest.children.length ≤ fanout :=
  manifest.bounded

/-- Aggregate manifests always name at least one direct child. -/
theorem AggregateManifest.has_child {fanout : Nat}
    {hasher : MerkleHasher} (manifest : AggregateManifest hasher fanout) :
    ∃ child, child ∈ manifest.children := by
  have positive : 0 < manifest.children.length :=
    Nat.pos_of_ne_zero manifest.nonempty
  let child := manifest.children.get 0 positive
  refine ⟨child, Vec.mem_iff_exists_get?.2 ?_⟩
  exact ⟨0, Vec.get?_eq_some_get manifest.children 0 positive⟩

end Grass.Build.Manifest
