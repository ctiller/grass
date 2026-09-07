import Grass.Build.Cache.Store

/-! # Collision-safe cache-store fixtures -/

namespace Grass.Tests.Build.Cache.Store

open Grass.Build.Cache Grass.Specification Grass.Std.Logical

def digest : Digest := ⟨Vec.empty⟩

def constantHasher : MerkleHasher where
  leaf := fun _ => digest
  branch := fun _ _ => digest

def environment (sourceValue : Nat) : SemanticEnvironment where
  source := ⟨Vec.singleton (BitVec.ofNat 8 sourceValue)⟩
  importedSummaries := Vec.empty
  semanticProfile := digest
  verifier := digest
  toolchain := digest
  generator := digest
  options := digest
  auditPolicy := digest

def Certificate (_ : SemanticEnvironment) := Unit

def entry (sourceValue : Nat) : CertifiedCacheEntry constantHasher Certificate where
  record := {
    environment := environment sourceValue
    key := digest
    keyExact := rfl
  }
  certificate := ()

def collidingStore : CacheStore constantHasher Certificate where
  entries := Vec.singleton (entry 1) ++ Vec.singleton (entry 2)

example : (collidingStore.candidatesFor (environment 2)).length = 2 := by
  decide

/-- The first digest collision is skipped and the later exact entry replays. -/
example : (replayFromStore? (environment 2) collidingStore).isSome = true := by
  decide

/-- Digest agreement without an exact environment never authorizes replay. -/
example : replayFromStore? (environment 3) collidingStore = none := by
  decide

end Grass.Tests.Build.Cache.Store
