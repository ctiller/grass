import Grass.Construct.Source.Manifest

/-!
# Derived authored-source manifest fixtures

Fixtures pin exact boundary identities, exit/edge lists, structural origins,
instruction counts, and lookup from one authored AST.
-/

namespace Grass.Tests.Construct.SourceManifest

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private def blockId (name : String) : BlockId := ⟨⟨"test.manifest", name⟩⟩
private def exitTag (name : String) : ExitTag := ⟨⟨"test.manifest", name⟩⟩
private def fragmentId : FragmentId := ⟨⟨"test.manifest", "generated"⟩⟩
private def contract : BlockContract Nat :=
  ⟨fun _ => True, [⟨exitTag "done", fun _ => True⟩]⟩
private def first : Grass.Construct.Source.Block Nat String Nat String :=
  ⟨⟨blockId "first", contract,
      [⟨exitTag "done", .block (blockId "second")⟩]⟩,
    .generated fragmentId (.literal [1, 2]), ["entry"]⟩
private def second : Grass.Construct.Source.Block Nat String Nat String :=
  ⟨⟨blockId "second", contract,
      [⟨exitTag "done", .terminal "return"⟩]⟩,
    .literal [3], []⟩
private def source : Ast Nat String Nat String :=
  ⟨blockId "first", [first, second]⟩

example : source.manifest.entry = blockId "first" := rfl
example : source.manifest.blockIds = [blockId "first", blockId "second"] := by
  decide
example : source.manifest.blocks.map BlockManifest.declaredExits =
    [[exitTag "done"], [exitTag "done"]] := by decide
example : source.manifest.blocks.map BlockManifest.outgoing =
    [first.cfg.outgoing, second.cfg.outgoing] := by decide
example : source.manifest.blocks.map (fun block => block.origins.length) = [2, 1] :=
  by decide
example : source.manifest.instructionCount = 3 := by decide
example : source.manifest.findBlock? (blockId "second") =
    (source.findBlock? (blockId "second")).map
      Grass.Construct.Source.Block.manifest :=
  source.manifest_findBlock? (blockId "second")

end Grass.Tests.Construct.SourceManifest
