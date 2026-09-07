import Grass.Construct.Source.Close
import Tests.Construct.SourceDiscover

/-!
# Authored source closure fixtures

Fixtures accept exact structural selections and available items, then reject a
missing item and a duplicate available-set entry while preserving locations.
-/

namespace Grass.Tests.Construct.SourceClose

open Grass.CFG Grass.Construct.Source
open Grass.Tests.Construct.SourceAst Grass.Tests.Construct.SourceDiscover

def closed : Closure source model where
  joins := ⟨[]⟩
  loops := ⟨[]⟩
  available := ["read", "call"]

example : closed.WellFormed := by decide
example : closed.unresolvedLocated = [] := Closure.unresolvedLocated_eq_nil closed (by
  decide)

def missing : Closure source model where
  joins := ⟨[]⟩
  loops := ⟨[]⟩
  available := ["read"]

example : ¬ missing.WellFormed := by decide
example : missing.unresolvedLocated = [
    ⟨blockId "second", ⟨[], [0], 0⟩, 0, "call"⟩
  ] := by decide

def duplicate : Closure source model where
  joins := ⟨[]⟩
  loops := ⟨[]⟩
  available := ["read", "read", "call"]

example : ¬ duplicate.WellFormed := by decide

end Grass.Tests.Construct.SourceClose
