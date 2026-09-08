import Grass.Build.Cache.Store

/-! # Collision-safe cache-store fixtures -/

namespace Grass.Tests.Build.Cache.Store

open Grass.Build.Cache Grass.Specification Grass.Std.Logical

def digest : Digest := ⟨Vec.empty⟩

def constantHasher : MerkleHasher where
  leaf := fun _ => digest
  branch := fun _ _ => digest

def metadata (sourceValue : Nat) : SemanticEnvironmentMetadata where
  source := ⟨Vec.singleton (BitVec.ofNat 8 sourceValue)⟩
  importedSummaries := Vec.empty
  semanticProfile := digest
  verifier := digest
  toolchain := digest
  generator := digest
  options := digest
  auditPolicy := digest

def Certificate (_ : Nat) := Unit

def entry (sourceValue : Nat) : CertifiedCacheEntry constantHasher Nat metadata
    Certificate where
  exactEnvironment := sourceValue
  record := {
    metadata := metadata sourceValue
    key := digest
    keyExact := rfl
  }
  metadataExact := rfl
  certificate := ()

def collidingStore : CacheStore constantHasher Nat metadata Certificate where
  entries := Vec.singleton (entry 1) ++ Vec.singleton (entry 2)

example : (collidingStore.candidatesFor 2).length = 2 := by
  decide

/-- The first digest collision is skipped and the later exact entry replays. -/
example : (replayFromStore? 2 collidingStore).isSome = true := by
  decide

/-- Digest agreement without an exact environment never authorizes replay. -/
example : replayFromStore? 3 collidingStore = none := by
  decide

example :
    (replayFromStore? 2 collidingStore).isSome = true ↔
      ∃ candidate ∈ collidingStore.candidatesFor 2,
        ReplayEligible 2 candidate :=
  replayFromStore?_isSome_iff ..

end Grass.Tests.Build.Cache.Store
