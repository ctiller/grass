import Grass.Build.Manifest.Core

/-!
# Exact semantic-environment invalidation

`RebuildCause.differs` compares retained semantic-environment fields directly,
and `classifyInvalidation` selects a cache hit only from their structure equality.
-/

namespace Grass.Build.Manifest

open Grass.Build.Cache Grass.Std.Logical

/-- Whether one named semantic component differs between two environments. -/
def RebuildCause.differs (cause : RebuildCause)
    (cached requested : SemanticEnvironment) : Bool :=
  match cause with
  | .source => cached.source != requested.source
  | .importedSummary => cached.importedSummaries != requested.importedSummaries
  | .semanticProfile => cached.semanticProfile != requested.semanticProfile
  | .verifier => cached.verifier != requested.verifier
  | .toolchain => cached.toolchain != requested.toolchain
  | .generator => cached.generator != requested.generator
  | .options => cached.options != requested.options
  | .auditPolicy => cached.auditPolicy != requested.auditPolicy

/-- The canonical semantic-component order used in invalidation reports. -/
def allRebuildCauses : List RebuildCause :=
  [.source, .importedSummary, .semanticProfile, .verifier, .toolchain,
    .generator, .options, .auditPolicy]

/-- Every and only changed semantic component, in canonical report order. -/
def changedCauses (cached requested : SemanticEnvironment) : Vec RebuildCause :=
  Vec.fromList (allRebuildCauses.filter fun cause => cause.differs cached requested)

/-- Membership in `changedCauses` is exact, rather than merely diagnostic. -/
theorem mem_changedCauses_iff (cause : RebuildCause)
    (cached requested : SemanticEnvironment) :
    cause ∈ changedCauses cached requested ↔ cause.differs cached requested = true := by
  cases cause <;>
    simp [Vec.mem_iff_mem_toList, changedCauses, allRebuildCauses, RebuildCause.differs]

/-- Unequal environments always produce a nonempty cause vector. -/
theorem changedCauses_nonempty {cached requested : SemanticEnvironment}
    (different : cached ≠ requested) :
    (changedCauses cached requested).length ≠ 0 := by
  intro lengthZero
  have empty : changedCauses cached requested = Vec.empty :=
    (Vec.eq_empty_iff_length_eq_zero _).2 lengthZero
  have sameSource : cached.source = requested.source := by
    by_cases same : cached.source = requested.source
    · exact same
    have present : RebuildCause.source ∈ changedCauses cached requested :=
      (mem_changedCauses_iff ..).2 (by simp [RebuildCause.differs, same])
    rw [empty] at present
    simp at present
  have sameImports : cached.importedSummaries = requested.importedSummaries := by
    by_cases same : cached.importedSummaries = requested.importedSummaries
    · exact same
    have present : RebuildCause.importedSummary ∈ changedCauses cached requested :=
      (mem_changedCauses_iff ..).2 (by simp [RebuildCause.differs, same])
    rw [empty] at present
    simp at present
  have sameProfile : cached.semanticProfile = requested.semanticProfile := by
    by_cases same : cached.semanticProfile = requested.semanticProfile
    · exact same
    have present : RebuildCause.semanticProfile ∈ changedCauses cached requested :=
      (mem_changedCauses_iff ..).2 (by simp [RebuildCause.differs, same])
    rw [empty] at present
    simp at present
  have sameVerifier : cached.verifier = requested.verifier := by
    by_cases same : cached.verifier = requested.verifier
    · exact same
    have present : RebuildCause.verifier ∈ changedCauses cached requested :=
      (mem_changedCauses_iff ..).2 (by simp [RebuildCause.differs, same])
    rw [empty] at present
    simp at present
  have sameToolchain : cached.toolchain = requested.toolchain := by
    by_cases same : cached.toolchain = requested.toolchain
    · exact same
    have present : RebuildCause.toolchain ∈ changedCauses cached requested :=
      (mem_changedCauses_iff ..).2 (by simp [RebuildCause.differs, same])
    rw [empty] at present
    simp at present
  have sameGenerator : cached.generator = requested.generator := by
    by_cases same : cached.generator = requested.generator
    · exact same
    have present : RebuildCause.generator ∈ changedCauses cached requested :=
      (mem_changedCauses_iff ..).2 (by simp [RebuildCause.differs, same])
    rw [empty] at present
    simp at present
  have sameOptions : cached.options = requested.options := by
    by_cases same : cached.options = requested.options
    · exact same
    have present : RebuildCause.options ∈ changedCauses cached requested :=
      (mem_changedCauses_iff ..).2 (by simp [RebuildCause.differs, same])
    rw [empty] at present
    simp at present
  have sameAudit : cached.auditPolicy = requested.auditPolicy := by
    by_cases same : cached.auditPolicy = requested.auditPolicy
    · exact same
    have present : RebuildCause.auditPolicy ∈ changedCauses cached requested :=
      (mem_changedCauses_iff ..).2 (by simp [RebuildCause.differs, same])
    rw [empty] at present
    simp at present
  apply different
  cases cached
  cases requested
  simp_all

/-- Classify an incremental request from exact environments. Equality yields a
cache hit; inequality yields every changed component and its nonemptiness proof. -/
def classifyInvalidation (cached requested : SemanticEnvironment) : BuildDisposition :=
  if same : cached = requested then
    .cacheHit
  else
    .rebuilt (changedCauses cached requested) (changedCauses_nonempty same)

/-- Exact environment equality is precisely the cache-hit case. -/
theorem classifyInvalidation_eq_cacheHit_iff
    (cached requested : SemanticEnvironment) :
    classifyInvalidation cached requested = .cacheHit ↔ cached = requested := by
  simp [classifyInvalidation]

end Grass.Build.Manifest
