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

def firstImport : ImportedSummary where
  scope := ScopeId.root.child "first"
  summary := ⟨Vec.singleton 1⟩

def secondImport : ImportedSummary where
  scope := ScopeId.root.child "second"
  summary := ⟨Vec.singleton 2⟩

def orderedImports : Vec ImportedSummary :=
  Vec.fromList [firstImport, secondImport]

def reversedImports : Vec ImportedSummary :=
  Vec.fromList [secondImport, firstImport]

example : importedSummariesTree orderedImports ≠
    importedSummariesTree reversedImports := by
  apply importedSummariesTree_ne_of_ne
  decide

example : importedSummariesTree (Vec.singleton firstImport) ≠
    importedSummariesTree orderedImports := by
  apply importedSummariesTree_ne_of_ne
  decide

example : cacheKey constantHasher environmentA = cacheKey constantHasher environmentB := rfl

example : environmentA ≠ environmentB := by decide

def recordA : CacheRecord constantHasher where
  environment := environmentA
  key := cacheKey constantHasher environmentA
  keyExact := rfl

example : ¬ReplayEligible environmentB recordA := by
  unfold ReplayEligible recordA
  decide

example : ReplayEligible environmentA recordA := rfl

end Grass.Tests.Build.Cache
