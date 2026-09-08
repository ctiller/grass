import Grass.Specification.Scope
import Grass.Std.Logical.Vec

/-!
# Semantic-environment cache keys

Cache digests are lookup aids, never proof authority. This module therefore
keeps the exact semantic environment beside its Merkle key and defines replay
eligibility by environment equality, not digest equality.
-/

namespace Grass.Build.Cache

open Grass.Specification Grass.Std.Logical

/-- Opaque digest bytes used for cache lookup. No collision-resistance theorem
is assumed by the logical model. -/
structure Digest where
  bytes : Std.Logical.ByteArray
  deriving DecidableEq, Repr

/-- One imported public summary in its deterministic input order. Exact replay
compares this data structurally, including the nominal scope identity. -/
structure ImportedSummary where
  scope : ScopeId
  summary : Digest
  deriving DecidableEq, Repr

/-- Every semantic input which may change a cached proof or artifact. The import
sequence is retained rather than replaced by its root digest. -/
structure SemanticEnvironment where
  source : Digest
  importedSummaries : Vec ImportedSummary
  semanticProfile : Digest
  verifier : Digest
  toolchain : Digest
  generator : Digest
  options : Digest
  auditPolicy : Digest
  deriving DecidableEq, Repr

/-- `MerkleAtom` represents each semantic domain with a distinct constructor;
for example, a source digest and toolchain digest remain different preimages.
No injectivity or collision-resistance property of their digests follows. -/
inductive MerkleAtom where
  | source (digest : Digest)
  | importScope (scope : ScopeId)
  | importSummary (digest : Digest)
  | noMoreImports
  | semanticProfile (digest : Digest)
  | verifier (digest : Digest)
  | toolchain (digest : Digest)
  | generator (digest : Digest)
  | options (digest : Digest)
  | auditPolicy (digest : Digest)
  deriving DecidableEq, Repr

/-- A proof-independent Merkle preimage. Tree shape and leaf domains are part of
the cache-key definition, while the concrete digest algorithm is replaceable. -/
inductive MerkleTree where
  | leaf (atom : MerkleAtom)
  | branch (left right : MerkleTree)
  deriving DecidableEq, Repr

/-- A concrete Merkle digest implementation. Soundness never assumes this
function is injective. -/
structure MerkleHasher where
  leaf : MerkleAtom → Digest
  branch : Digest → Digest → Digest

/-- Fold the explicit preimage with a selected digest implementation. -/
def MerkleTree.digest (hasher : MerkleHasher) : MerkleTree → Digest
  | .leaf atom => hasher.leaf atom
  | .branch left right =>
      hasher.branch (left.digest hasher) (right.digest hasher)

/-- `importedSummariesTree` retains import order and ends it with an explicit
`MerkleAtom.noMoreImports` leaf. This distinguishes the tree preimages for
extension and final-entry replacement; a selected hasher may still collide. -/
def importedSummariesTree (imports : Vec ImportedSummary) : MerkleTree :=
  imports.foldr
    (fun imported rest =>
      .branch
        (.branch (.leaf (.importScope imported.scope))
          (.leaf (.importSummary imported.summary)))
        rest)
    (.leaf .noMoreImports)

/-- `importedSummariesTree_injective` proves that the canonical Merkle preimage
retains the complete ordered import sequence, before any selected hasher is
applied. -/
theorem importedSummariesTree_injective :
    ∀ first second : Vec ImportedSummary,
      importedSummariesTree first = importedSummariesTree second →
        first = second := by
  intro first
  induction first using Vec.recOnCons with
  | empty =>
    intro second
    induction second using Vec.recOnCons with
    | empty => intro _; rfl
    | cons imported rest _ =>
      intro equality
      simp [importedSummariesTree] at equality
  | cons imported rest inductionHypothesis =>
    intro second
    induction second using Vec.recOnCons with
    | empty =>
      intro equality
      simp [importedSummariesTree] at equality
    | cons other tail _ =>
      intro equality
      obtain ⟨scope, summary⟩ := imported
      obtain ⟨otherScope, otherSummary⟩ := other
      simp only [importedSummariesTree, Vec.foldr_cons,
        MerkleTree.branch.injEq, MerkleTree.leaf.injEq,
        MerkleAtom.importScope.injEq, MerkleAtom.importSummary.injEq] at equality
      obtain ⟨⟨scopeExact, summaryExact⟩, tailExact⟩ := equality
      have restExact : rest = tail := inductionHypothesis tail (by
        simpa [importedSummariesTree] using tailExact)
      subst restExact
      subst scopeExact
      subst summaryExact
      rfl

/-- Distinct ordered import sequences have distinct canonical preimage trees. -/
theorem importedSummariesTree_ne_of_ne
    {first second : Vec ImportedSummary} (different : first ≠ second) :
    importedSummariesTree first ≠ importedSummariesTree second :=
  fun equality => different
    (importedSummariesTree_injective first second equality)

/-- Canonical tree shape for every semantic-environment component. -/
def SemanticEnvironment.merkleTree (environment : SemanticEnvironment) : MerkleTree :=
  let audit := .leaf (.auditPolicy environment.auditPolicy)
  let options := .branch (.leaf (.options environment.options)) audit
  let generator := .branch (.leaf (.generator environment.generator)) options
  let toolchain := .branch (.leaf (.toolchain environment.toolchain)) generator
  let verifier := .branch (.leaf (.verifier environment.verifier)) toolchain
  let profile := .branch (.leaf (.semanticProfile environment.semanticProfile)) verifier
  let imports := .branch (importedSummariesTree environment.importedSummaries) profile
  .branch (.leaf (.source environment.source)) imports

/-- The lookup key produced from the complete semantic environment. -/
def cacheKey (hasher : MerkleHasher) (environment : SemanticEnvironment) : Digest :=
  environment.merkleTree.digest hasher

/-- A cache index entry retains the exact environment whose digest it stores. -/
structure CacheRecord (hasher : MerkleHasher) where
  environment : SemanticEnvironment
  key : Digest
  keyExact : cacheKey hasher environment = key

/-- Replay is eligible only for the exact reconstructed semantic environment.
The cached digest is deliberately absent from this predicate. -/
def ReplayEligible {hasher : MerkleHasher}
    (requested : SemanticEnvironment) (record : CacheRecord hasher) : Prop :=
  requested = record.environment

/-- Exact environment reconstruction implies that the stored lookup key is the
key of the requested environment. The converse is intentionally unavailable. -/
theorem ReplayEligible.key_matches {hasher : MerkleHasher}
    {requested : SemanticEnvironment} {record : CacheRecord hasher}
    (eligible : ReplayEligible requested record) :
    record.key = cacheKey hasher requested := by
  subst requested
  exact record.keyExact.symm

end Grass.Build.Cache
