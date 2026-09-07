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

def environmentA : SemanticEnvironment where
  source := ⟨Vec.singleton 0⟩
  importedSummaries := Vec.empty
  semanticProfile := emptyDigest
  verifier := emptyDigest
  toolchain := emptyDigest
  generator := emptyDigest
  options := emptyDigest
  auditPolicy := emptyDigest

def environmentB : SemanticEnvironment :=
  { environmentA with source := ⟨Vec.singleton 1⟩ }

structure ExactCertificate (environment : SemanticEnvironment) : Type where
  exact : environment = environmentA

def entryA : CertifiedCacheEntry constantHasher ExactCertificate where
  record :=
    { environment := environmentA
      key := cacheKey constantHasher environmentA
      keyExact := rfl }
  certificate := ⟨rfl⟩

example : cacheKey constantHasher environmentA = cacheKey constantHasher environmentB := rfl

example : (replay? environmentA entryA).isSome = true := by
  exact (replay?_isSome_iff environmentA entryA).2 rfl

example : replay? environmentB entryA = none := by
  apply (replay?_eq_none_iff environmentB entryA).2
  unfold ReplayEligible entryA
  decide

end ReplayFixture

end Grass.Tests.Build.Cache
