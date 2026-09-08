import Grass.Build.Cache.Replay

/-! # Exact-environment certificate replay fixtures -/

namespace Grass.Tests.Build.Cache

open Grass.Build.Cache Grass.Std.Logical

namespace ReplayFixture

def emptyDigest : Digest := ⟨Vec.empty⟩

/-- This deliberately collides for all environments. Replay must remain exact
even when the lookup layer supplies no discrimination at all. -/
def constantHasher : MerkleHasher where
  leaf _ := emptyDigest
  branch _ _ := emptyDigest

def sharedMetadata : SemanticEnvironmentMetadata where
  source := ⟨Vec.singleton 0⟩
  importedSummaries := Vec.empty
  semanticProfile := emptyDigest
  verifier := emptyDigest
  toolchain := emptyDigest
  generator := emptyDigest
  options := emptyDigest
  auditPolicy := emptyDigest

inductive ActualSource where
  | a
  | b
  deriving DecidableEq, Repr

def metadataOf (_ : ActualSource) : SemanticEnvironmentMetadata :=
  sharedMetadata

structure ExactCertificate (source : ActualSource) : Type where
  exact : source = .a

def entryA : CertifiedCacheEntry constantHasher ActualSource metadataOf
    ExactCertificate where
  exactEnvironment := .a
  record :=
    { metadata := sharedMetadata
      key := cacheKey constantHasher sharedMetadata
      keyExact := rfl }
  metadataExact := rfl
  certificate := ⟨rfl⟩

example : ActualSource.a ≠ ActualSource.b := by decide

example : metadataOf .a = metadataOf .b := rfl

example : cacheKey constantHasher (metadataOf .a) =
    cacheKey constantHasher (metadataOf .b) := rfl

example : (replay? ActualSource.a entryA).isSome = true := by
  exact (replay?_isSome_iff ActualSource.a entryA).2 rfl

example : ExactCertificate ActualSource.a :=
  replayExact entryA rfl

example : replay? ActualSource.b entryA = none := by
  apply (replay?_eq_none_iff ActualSource.b entryA).2
  unfold ReplayEligible
  decide

end ReplayFixture

end Grass.Tests.Build.Cache
