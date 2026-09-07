import Grass.Construct.Fragment.Manifest

/-!
# Derived fragment-manifest fixtures

The fixtures retain repeated demand occurrences, prove generator wrapping does
not change a manifest, and reject missing or duplicate available items.
-/

namespace Grass.Tests.Construct.FragmentManifest

open Grass Grass.Construct.Fragment

def fragmentId (name : String) : FragmentId := ⟨⟨"test.manifest", name⟩⟩

inductive Instruction where
  | use (items : List String)
  | idle
deriving Repr, DecidableEq

def references : ManifestModel Instruction String where
  project
    | .use items => items
    | .idle => []

def source : Source Instruction :=
  .generated (fragmentId "outer") (.sequence [
    .literal [.use ["alpha", "beta"], .idle],
    .generated (fragmentId "inner") (.literal [.use ["alpha"]])
  ])

example : source.manifest references = ["alpha", "beta", "alpha"] := by decide

example :
    (Source.generated (fragmentId "other") source).manifest references =
      source.manifest references := by simp

def closed : ManifestClosure source references where
  available := ["alpha", "beta", "unused"]

example : closed.WellFormed := by decide
example : closed.unresolved = [] := by decide

def missing : ManifestClosure source references where
  available := ["alpha"]

example : missing.unresolved = ["beta"] := by decide
example : ¬ missing.WellFormed := by decide

def noneAvailable : ManifestClosure source references where
  available := []

example : noneAvailable.unresolved = ["alpha", "beta", "alpha"] := by decide
example : ¬ noneAvailable.WellFormed := by decide

def duplicateAvailable : ManifestClosure source references where
  available := ["alpha", "alpha", "beta"]

example : ¬ duplicateAvailable.WellFormed := by decide

end Grass.Tests.Construct.FragmentManifest
