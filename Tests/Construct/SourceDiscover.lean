import Grass.Construct.Source.Discover
import Tests.Construct.SourceAst

/-!
# Authored discovery fixtures

The fixtures derive repeated generic demands with exact block, generator,
child-path, literal, and per-instruction projection indices from the AST fixture.
-/

namespace Grass.Tests.Construct.SourceDiscover

open Grass.CFG Grass.Construct.Fragment Grass.Construct.Source
open Grass.Tests.Construct.SourceAst

def model : ManifestModel Nat String where
  project
    | 1 => ["read", "read"]
    | 3 => ["call"]
    | _ => []

example : source.itemManifest model = ["read", "read", "call"] := by native_decide

example : (source.discoverItems model).map LocatedItem.item =
    source.itemManifest model := Ast.discoveredItems_exact source model

example : source.discoverItems model = [
    ⟨blockId "first", ⟨[fragmentId "pair"], [], 0⟩, 0, "read"⟩,
    ⟨blockId "first", ⟨[fragmentId "pair"], [], 0⟩, 1, "read"⟩,
    ⟨blockId "second", ⟨[], [0], 0⟩, 0, "call"⟩
  ] := by native_decide

example : (source.discover model).graph = source.toGraph := rfl
example : (source.discover model).joins = [] := by native_decide
example : (source.discover model).loops = [] := by native_decide

end Grass.Tests.Construct.SourceDiscover
