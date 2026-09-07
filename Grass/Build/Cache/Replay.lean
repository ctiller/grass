import Grass.Build.Cache.Key

/-!
# Exact-environment certificate replay

The certificate family is supplied by its owning verification layer and is
indexed by the full semantic environment. Cache replay only transports an
existing certificate across a proved environment equality.
-/

namespace Grass.Build.Cache

/-- A cached certificate paired with the exact environment and lookup key under
which it was produced. `Certificate` remains an external indexed gate. -/
structure CertifiedCacheEntry (hasher : MerkleHasher)
    (Certificate : SemanticEnvironment → Type) where
  record : CacheRecord hasher
  certificate : Certificate record.environment

/-- Attempt to replay a certificate in a reconstructed environment. Digest
agreement is not inspected; only decidable equality of the retained environment
can change the certificate's index. -/
def replay? {hasher : MerkleHasher} {Certificate : SemanticEnvironment → Type}
    (requested : SemanticEnvironment)
    (entry : CertifiedCacheEntry hasher Certificate) : Option (Certificate requested) :=
  if equal : requested = entry.record.environment then
    some (equal.symm ▸ entry.certificate)
  else
    none

/-- A replay result exists exactly when the cache record is eligible under the
full-environment equality predicate. -/
theorem replay?_isSome_iff {hasher : MerkleHasher}
    {Certificate : SemanticEnvironment → Type}
    (requested : SemanticEnvironment)
    (entry : CertifiedCacheEntry hasher Certificate) :
    (replay? requested entry).isSome = true ↔
      ReplayEligible requested entry.record := by
  simp [replay?, ReplayEligible]

/-- Failure is likewise exact: replay returns none precisely for an environment
mismatch, independently of the stored Merkle digest. -/
theorem replay?_eq_none_iff {hasher : MerkleHasher}
    {Certificate : SemanticEnvironment → Type}
    (requested : SemanticEnvironment)
    (entry : CertifiedCacheEntry hasher Certificate) :
    replay? requested entry = none ↔
      ¬ReplayEligible requested entry.record := by
  simp [replay?, ReplayEligible]

end Grass.Build.Cache
