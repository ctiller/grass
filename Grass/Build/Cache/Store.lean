import Grass.Build.Cache.Replay

/-!
# Collision-safe certificate cache store

`CacheStore.candidatesFor` uses Merkle keys only to locate candidates.
`replayFromStore?` then scans those candidates for exact environment equality.
-/

namespace Grass.Build.Cache

open Grass.Std.Logical

/-- A finite collection of certified entries for one certificate family. -/
structure CacheStore (hasher : MerkleHasher)
    (Certificate : SemanticEnvironment → Type) where
  entries : Vec (CertifiedCacheEntry hasher Certificate)

/-- Hash-located candidates for a request. A collision may put several distinct
environments in this vector, so membership conveys no replay authority. -/
def CacheStore.candidatesFor {hasher : MerkleHasher}
    {Certificate : SemanticEnvironment → Type}
    (store : CacheStore hasher Certificate)
    (requested : SemanticEnvironment) : Vec (CertifiedCacheEntry hasher Certificate) :=
  Vec.fromList <| store.entries.toList.filter fun entry =>
    entry.record.key == cacheKey hasher requested

/-- Scan a candidate list until exact environment equality permits dependent
transport of the retained certificate. -/
def replayCandidates? {hasher : MerkleHasher}
    {Certificate : SemanticEnvironment → Type}
    (requested : SemanticEnvironment) :
    List (CertifiedCacheEntry hasher Certificate) → Option (Certificate requested)
  | [] => none
  | entry :: rest =>
      if equal : requested = entry.record.environment then
        some (equal.symm ▸ entry.certificate)
      else
        replayCandidates? requested rest

/-- Locate by Merkle key, then authorize replay only by exact retained
environment equality. A colliding first candidate does not shadow a later
eligible entry. -/
def replayFromStore? {hasher : MerkleHasher}
    {Certificate : SemanticEnvironment → Type}
    (requested : SemanticEnvironment)
    (store : CacheStore hasher Certificate) : Option (Certificate requested) :=
  replayCandidates? requested (store.candidatesFor requested).toList

/-- A mismatched candidate is skipped rather than accepted or treated as a
terminal lookup result. -/
@[simp] theorem replayCandidates?_cons_mismatch {hasher : MerkleHasher}
    {Certificate : SemanticEnvironment → Type}
    (requested : SemanticEnvironment)
    (entry : CertifiedCacheEntry hasher Certificate)
    (rest : List (CertifiedCacheEntry hasher Certificate))
    (mismatch : requested ≠ entry.record.environment) :
    replayCandidates? requested (entry :: rest) = replayCandidates? requested rest := by
  simp [replayCandidates?, mismatch]

/-- An exactly matching head candidate replays its retained certificate. -/
@[simp] theorem replayCandidates?_cons_match {hasher : MerkleHasher}
    {Certificate : SemanticEnvironment → Type}
    (environment : SemanticEnvironment)
    (entry : CertifiedCacheEntry hasher Certificate)
    (rest : List (CertifiedCacheEntry hasher Certificate))
    (matchEnvironment : environment = entry.record.environment) :
    replayCandidates? environment (entry :: rest) =
      some (matchEnvironment.symm ▸ entry.certificate) := by
  simp [replayCandidates?, matchEnvironment]

end Grass.Build.Cache
