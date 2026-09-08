import Grass.Build.Manifest.Core

/-! # Bounded manifest and composition-certificate fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Cache Grass.Build.Manifest Grass.Specification Grass.Std.Logical

def emptyDigest : Digest := ⟨Vec.empty⟩

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

def aggregate : AggregateManifest 2 where
  scope := ScopeId.root
  children := twoChildren
  nonempty := by simp [twoChildren]
  bounded := by simp [twoChildren]
  manifestRoot := emptyDigest
  publicSummary := emptyDigest
  measurement := measurement

example : aggregate.children.length ≤ 2 := aggregate.children_bounded

example : ∃ child, child ∈ aggregate.children := aggregate.has_child

/-- A fanout-one aggregate cannot carry the two-child fixture. -/
example : ¬∃ candidate : AggregateManifest 1, candidate.children = twoChildren := by
  rintro ⟨candidate, childrenEq⟩
  have bounded := candidate.children_bounded
  rw [childrenEq] at bounded
  simp [twoChildren] at bounded

def CountsChildren (children : Vec ChildSummary) (summary : Nat) : Prop :=
  summary = children.length

def aggregateCertificate : AggregateCertificate aggregate Nat CountsChildren where
  summary := 2
  composition := by simp [CountsChildren, aggregate, twoChildren]

example : CountsChildren aggregate.children aggregateCertificate.summary :=
  aggregateCertificate.composition

end Grass.Tests.Build.Manifest
