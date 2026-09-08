import Grass.Specification.Scope
import Grass.Std.Logical.Vec

/-!
# Semantic-environment cache keys

Cache digests and their structured metadata are lookup aids, never proof
authority. Exact proof indices are retained separately by `CertifiedCacheEntry`
in `Grass.Build.Cache.Replay`.
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

/-- Digest metadata for every semantic input which may change a cached proof or
artifact. This is a lookup/invalidation preimage, not an exact proof index. -/
structure SemanticEnvironmentMetadata where
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

/-- Canonical tree shape for every semantic-environment component. -/
def SemanticEnvironmentMetadata.merkleTree
    (environment : SemanticEnvironmentMetadata) : MerkleTree :=
  let audit := .leaf (.auditPolicy environment.auditPolicy)
  let options := .branch (.leaf (.options environment.options)) audit
  let generator := .branch (.leaf (.generator environment.generator)) options
  let toolchain := .branch (.leaf (.toolchain environment.toolchain)) generator
  let verifier := .branch (.leaf (.verifier environment.verifier)) toolchain
  let profile := .branch (.leaf (.semanticProfile environment.semanticProfile)) verifier
  let imports := .branch (importedSummariesTree environment.importedSummaries) profile
  .branch (.leaf (.source environment.source)) imports

/-- The lookup key produced from the complete semantic environment. -/
def cacheKey (hasher : MerkleHasher)
    (environment : SemanticEnvironmentMetadata) : Digest :=
  environment.merkleTree.digest hasher

/-- A cache index record retains the complete digest metadata behind its key.
Neither this record nor equality of its fields authorizes proof transport. -/
structure CacheRecord (hasher : MerkleHasher) where
  metadata : SemanticEnvironmentMetadata
  key : Digest
  keyExact : cacheKey hasher metadata = key

end Grass.Build.Cache
