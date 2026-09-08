import Grass.Build.Cache.Key

/-! # Semantic-environment cache-key fixtures -/

namespace Grass.Tests.Build.Cache

open Grass.Build.Cache Grass.Specification Grass.Std.Logical

def emptyDigest : Digest := ⟨Vec.empty⟩

/-- A deliberately colliding hasher used to show that digest equality cannot
authorize certificate replay. -/
def constantHasher : MerkleHasher where
  leaf _ := emptyDigest
  branch _ _ := emptyDigest

def environmentA : SemanticEnvironmentMetadata where
  source := ⟨Vec.singleton 0⟩
  importedSummaries := Vec.empty
  semanticProfile := emptyDigest
  verifier := emptyDigest
  toolchain := emptyDigest
  generator := emptyDigest
  options := emptyDigest
  auditPolicy := emptyDigest

def environmentB : SemanticEnvironmentMetadata :=
  { environmentA with source := ⟨Vec.singleton 1⟩ }

example : cacheKey constantHasher environmentA = cacheKey constantHasher environmentB := rfl

example : environmentA ≠ environmentB := by decide

def recordA : CacheRecord constantHasher where
  metadata := environmentA
  key := cacheKey constantHasher environmentA
  keyExact := rfl

end Grass.Tests.Build.Cache
