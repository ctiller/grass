import Grass.Build.Manifest.Core

/-! # Bounded manifest and composition-certificate fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Cache Grass.Build.Manifest Grass.Specification Grass.Std.Logical

def emptyDigest : Digest := ⟨Vec.empty⟩

def hasher : MerkleHasher where
  leaf _ := emptyDigest
  branch _ _ := emptyDigest

def measurement : BuildMeasurement where
  elapsedNanoseconds := 10
  peakResidentBytes := 20
  oleanBytes := 30
  proofBytes := 40
  artifactBytes := 50

def firstChild : ChildSummary where
  scope := ScopeId.root.child "first"
  manifestRoot := emptyDigest
  publicSummary := emptyDigest

def secondChild : ChildSummary where
  scope := ScopeId.root.child "second"
  manifestRoot := emptyDigest
  publicSummary := emptyDigest

def twoChildren : Vec ChildSummary :=
  Vec.singleton firstChild ++ Vec.singleton secondChild

def aggregate : AggregateManifest hasher 2 where
  scope := ScopeId.root
  children := twoChildren
  nonempty := by simp [twoChildren]
  bounded := by simp [twoChildren]
  publicSummary := emptyDigest
  measurement := measurement

example : aggregate.children.length ≤ 2 := aggregate.children_bounded

example : ∃ child, child ∈ aggregate.children := aggregate.has_child

/-- A fanout-one aggregate cannot carry the two-child fixture. -/
example : ¬∃ candidate : AggregateManifest hasher 1,
    candidate.children = twoChildren := by
  rintro ⟨candidate, childrenEq⟩
  have bounded := candidate.children_bounded
  rw [childrenEq] at bounded
  simp [twoChildren] at bounded

example : aggregate.manifestRoot = emptyDigest := rfl
example : aggregate.childSummary.manifestRoot = aggregate.manifestRoot := rfl

end Grass.Tests.Build.Manifest
