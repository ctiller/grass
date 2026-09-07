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

/-- A leaf records its nominal scope, exact keyed semantic environment, compact
public and artifact digests, observed costs, and build disposition. -/
structure LeafManifest (hasher : MerkleHasher) where
  scope : ScopeId
  cache : CacheRecord hasher
  publicSummary : Digest
  artifact : Digest
  measurement : BuildMeasurement
  disposition : BuildDisposition

/-- The compact information an aggregate retains for one direct child. It does
not contain the child's source, proof, artifact bytes, or descendant list. -/
structure ChildSummary where
  scope : ScopeId
  manifestRoot : Digest
  publicSummary : Digest
  deriving DecidableEq, Repr

/-- One bounded-fanout aggregate node over direct child summaries. `fanout` is a
type index, so every consumer receives the bound proof with the value. -/
structure AggregateManifest (fanout : Nat) where
  scope : ScopeId
  children : Vec ChildSummary
  nonempty : children.length ≠ 0
  bounded : children.length ≤ fanout
  manifestRoot : Digest
  measurement : BuildMeasurement

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
