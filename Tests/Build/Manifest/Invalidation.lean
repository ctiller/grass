import Grass.Build.Manifest.Invalidation

/-! # Exact invalidation classification fixtures -/

namespace Grass.Tests.Build.Manifest.Invalidation

open Grass.Build.Cache Grass.Build.Manifest Grass.Specification Grass.Std.Logical

def digest (value : Nat) : Digest := ⟨Vec.singleton (BitVec.ofNat 8 value)⟩

def base : SemanticEnvironment where
  source := digest 1
  importedSummaries := Vec.empty
  semanticProfile := digest 2
  verifier := digest 3
  toolchain := digest 4
  generator := digest 5
  options := digest 6
  auditPolicy := digest 7

def changed : SemanticEnvironment :=
  { base with
    source := digest 8
    options := digest 9 }

example : classifyInvalidation base base = .cacheHit := by
  simp [classifyInvalidation]

example : RebuildCause.source ∈ changedCauses base changed := by
  rw [mem_changedCauses_iff]
  decide

example : RebuildCause.options ∈ changedCauses base changed := by
  rw [mem_changedCauses_iff]
  decide

example : RebuildCause.verifier ∉ changedCauses base changed := by
  rw [mem_changedCauses_iff]
  decide

example : classifyInvalidation base changed ≠ .cacheHit := by
  intro cacheHit
  have same := (classifyInvalidation_eq_cacheHit_iff base changed).1 cacheHit
  have different : base ≠ changed := by decide
  exact different same

end Grass.Tests.Build.Manifest.Invalidation
