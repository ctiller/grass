import Grass.Construct.Source.Elaborate

/-!
# Checked authored-source elaboration fixtures

Fixtures pin successful normalization-plus-manifest derivation, exact source
and annotation preservation, and propagation of structural alpha failures.
-/

namespace Grass.Tests.Construct.SourceElaborate

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private def blockId : BlockId := ⟨⟨"test.elaborate", "entry"⟩⟩
private def tag : ExitTag := ⟨⟨"test.elaborate", "done"⟩⟩
private def contract : BlockContract Nat :=
  ⟨fun _ => True, [⟨tag, fun _ => True⟩]⟩
private def block : PreAlphaBlock Nat String Nat String :=
  ⟨.stable blockId, contract, [⟨tag, .terminal "return"⟩],
    .literal [4, 5, 6], ["reviewed"]⟩
private def source : PreAlphaAst Nat String Nat String :=
  ⟨.stable blockId, [block]⟩

private theorem sourceWellFormed (model : LabelAlphaModel) :
    (source.alphaNormalize model).WellFormed := by
  simp [source, block, contract, tag, Ast.WellFormed, Ast.toGraph,
    CFG.Graph.WellFormed, CFG.Graph.wellFormed, CFG.Graph.blockIds,
    CFG.Graph.findBlock?, CFG.Graph.targetsResolved, CFG.Graph.outgoingUnique,
    CFG.Graph.edgesDeclared, CFG.Graph.exitsCovered, CFG.Graph.outgoingTags,
    BlockContract.wellFormed, BlockContract.exitTags,
    BlockContract.declaresExit, PreAlphaAst.alphaNormalize,
    PreAlphaBlock.alphaNormalize, PreAlphaEdge.alphaNormalize,
    PreAlphaTarget.alphaNormalize]

private def result (model : LabelAlphaModel) : ElaboratedSource source model :=
  ⟨source.alphaNormalize model, (source.alphaNormalize model).manifest,
    rfl, rfl, sourceWellFormed model⟩

example (model : LabelAlphaModel) : (elaborate source model).isOk = true := by
  unfold elaborate checkAlpha
  rw [dif_pos (sourceWellFormed model)]
  rfl
example (model : LabelAlphaModel) :
    (result model).authored.blocks.flatMap (fun block => block.body.expand) =
      source.instructions :=
  (result model).instructionsExact
example (model : LabelAlphaModel) :
    (result model).authored.blocks.map Grass.Construct.Source.Block.annotations =
      [["reviewed"]] := by
  simpa [source, block] using (result model).annotationsExact
example (model : LabelAlphaModel) :
    (result model).manifest.entry = blockId :=
  (result model).manifestEntryExact
example (model : LabelAlphaModel) :
    (result model).manifest.blockIds = [blockId] := by
  rw [(result model).manifestBlockIdsExact]
  rfl
example (model : LabelAlphaModel) :
    (result model).manifest.instructionCount = 3 := by rfl

private def duplicateSource : PreAlphaAst Nat String Nat String :=
  ⟨.stable blockId, [block, block]⟩
private theorem duplicateInvalid (model : LabelAlphaModel) :
    ¬(duplicateSource.alphaNormalize model).WellFormed := by
  simp [duplicateSource, block, Ast.WellFormed, Ast.toGraph,
    CFG.Graph.WellFormed, CFG.Graph.wellFormed, CFG.Graph.blockIds,
    PreAlphaAst.alphaNormalize, PreAlphaBlock.alphaNormalize]

example (model : LabelAlphaModel) : elaborate duplicateSource model =
    .error ⟨blockId, [blockId, blockId], []⟩ := by
  unfold elaborate checkAlpha
  rw [dif_neg (duplicateInvalid model)]
  rfl

end Grass.Tests.Construct.SourceElaborate
