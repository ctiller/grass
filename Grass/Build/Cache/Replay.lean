import Grass.Build.Cache.Key

/-!
# Exact-index certificate replay

Digest metadata locates candidates. The certificate family is supplied by its
owning verification layer and indexed by an arbitrary exact environment value;
cache replay transports a certificate only across equality of that exact value.
-/

namespace Grass.Build.Cache

/-- A cached certificate retains its exact proof index separately from the
digest metadata used for lookup. `metadataOf` may collide for distinct exact
values without making those values replay-compatible. -/
structure CertifiedCacheEntry (hasher : MerkleHasher) (ExactEnvironment : Type)
    (metadataOf : ExactEnvironment → SemanticEnvironmentMetadata)
    (Certificate : ExactEnvironment → Type) where
  exactEnvironment : ExactEnvironment
  record : CacheRecord hasher
  metadataExact : record.metadata = metadataOf exactEnvironment
  certificate : Certificate exactEnvironment

/-- Replay eligibility is equality of exact proof indices. Digest metadata is
deliberately absent. -/
def ReplayEligible {hasher : MerkleHasher} {ExactEnvironment : Type}
    {metadataOf : ExactEnvironment → SemanticEnvironmentMetadata}
    {Certificate : ExactEnvironment → Type}
    (requested : ExactEnvironment)
    (entry : CertifiedCacheEntry hasher ExactEnvironment metadataOf Certificate) :
    Prop :=
  requested = entry.exactEnvironment

/-- Replay from a caller-supplied equality of exact proof indices. This path
does not require executable equality and therefore supports exact environments
containing propositions, specifications, or other kernel-owned values. -/
def replayExact {hasher : MerkleHasher} {ExactEnvironment : Type}
    {metadataOf : ExactEnvironment → SemanticEnvironmentMetadata}
    {Certificate : ExactEnvironment → Type}
    {requested : ExactEnvironment}
    (entry : CertifiedCacheEntry hasher ExactEnvironment metadataOf Certificate)
    (equal : requested = entry.exactEnvironment) : Certificate requested :=
  equal.symm ▸ entry.certificate

/-- Attempt to replay a certificate in a reconstructed environment. Digest
agreement is not inspected; only decidable equality of the retained environment
can change the certificate's index. -/
def replay? {hasher : MerkleHasher} {ExactEnvironment : Type}
    {metadataOf : ExactEnvironment → SemanticEnvironmentMetadata}
    {Certificate : ExactEnvironment → Type} [DecidableEq ExactEnvironment]
    (requested : ExactEnvironment)
    (entry : CertifiedCacheEntry hasher ExactEnvironment metadataOf Certificate) :
    Option (Certificate requested) :=
  if equal : requested = entry.exactEnvironment then
    some (replayExact entry equal)
  else
    none

/-- A replay result exists exactly when the cache record is eligible under the
full-environment equality predicate. -/
theorem replay?_isSome_iff {hasher : MerkleHasher}
    {ExactEnvironment : Type}
    {metadataOf : ExactEnvironment → SemanticEnvironmentMetadata}
    {Certificate : ExactEnvironment → Type} [DecidableEq ExactEnvironment]
    (requested : ExactEnvironment)
    (entry : CertifiedCacheEntry hasher ExactEnvironment metadataOf Certificate) :
    (replay? requested entry).isSome = true ↔
      ReplayEligible requested entry := by
  simp [replay?, ReplayEligible]

/-- Failure is likewise exact: replay returns none precisely for an environment
mismatch, independently of the stored Merkle digest. -/
theorem replay?_eq_none_iff {hasher : MerkleHasher}
    {ExactEnvironment : Type}
    {metadataOf : ExactEnvironment → SemanticEnvironmentMetadata}
    {Certificate : ExactEnvironment → Type} [DecidableEq ExactEnvironment]
    (requested : ExactEnvironment)
    (entry : CertifiedCacheEntry hasher ExactEnvironment metadataOf Certificate) :
    replay? requested entry = none ↔
      ¬ReplayEligible requested entry := by
  simp [replay?, ReplayEligible]

/-- Exact replay eligibility implies that the entry is discoverable under the
requested metadata key. The converse is unavailable because `metadataOf` and
the selected hasher may both collide. -/
theorem ReplayEligible.key_matches {hasher : MerkleHasher}
    {ExactEnvironment : Type}
    {metadataOf : ExactEnvironment → SemanticEnvironmentMetadata}
    {Certificate : ExactEnvironment → Type}
    {requested : ExactEnvironment}
    {entry : CertifiedCacheEntry hasher ExactEnvironment metadataOf Certificate}
    (eligible : ReplayEligible requested entry) :
    entry.record.key = cacheKey hasher (metadataOf requested) := by
  subst requested
  rw [← entry.metadataExact]
  exact entry.record.keyExact.symm

end Grass.Build.Cache
