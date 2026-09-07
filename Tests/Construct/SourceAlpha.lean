import Grass.Construct.Source.Alpha

/-!
# Pre-alpha authored CFG fixtures

Fixtures pin local entry/block/edge resolution through one model, preservation
of exact source and annotations, structural closure, and collision rejection.
-/

namespace Grass.Tests.Construct.SourceAlpha

open Grass Grass.Core Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private def supply : LabelSupply := FreshSupply.initial
private def minted : MintedLabel supply := supply.mint "loop"
private def tag : ExitTag := ⟨⟨"test.alpha", "again"⟩⟩
private def contract : BlockContract Nat :=
  ⟨fun _ => True, [⟨tag, fun _ => True⟩]⟩
private def block : PreAlphaBlock Nat Unit Nat String where
  label := .local minted.token
  contract := contract
  outgoing := [⟨tag, .label (.local minted.token)⟩]
  body := .literal [1, 2, 3]
  annotations := ["loop-header"]
private def source : PreAlphaAst Nat Unit Nat String :=
  ⟨.local minted.token, [block]⟩

example (model : LabelAlphaModel) :
    (source.alphaNormalize model).entry = model.toBlock minted.token.id := rfl
example (model : LabelAlphaModel) :
    (source.alphaNormalize model).blocks.head?.map (fun block => block.cfg.outgoing) =
      some [⟨tag, .block (model.toBlock minted.token.id)⟩] := by rfl
example (model : LabelAlphaModel) :
    ((source.alphaNormalize model).blocks.flatMap fun block => block.body.expand) =
      source.instructions := by simp
example (model : LabelAlphaModel) :
    (source.alphaNormalize model).blocks.map
      Grass.Construct.Source.Block.annotations = [["loop-header"]] := by
  simp [source, block, PreAlphaAst.alphaNormalize, PreAlphaBlock.alphaNormalize]

private theorem sourceWellFormed (model : LabelAlphaModel) :
    (source.alphaNormalize model).WellFormed := by
  simp [source, block, contract, tag, Ast.WellFormed, Ast.toGraph,
    CFG.Graph.WellFormed, CFG.Graph.wellFormed,
    CFG.Graph.blockIds, CFG.Graph.findBlock?, CFG.Graph.targetsResolved,
    CFG.Graph.outgoingUnique, CFG.Graph.edgesDeclared, CFG.Graph.exitsCovered,
    CFG.Graph.outgoingTags, BlockContract.wellFormed, BlockContract.exitTags,
    BlockContract.declaresExit, PreAlphaAst.alphaNormalize,
    PreAlphaBlock.alphaNormalize, PreAlphaEdge.alphaNormalize,
    PreAlphaTarget.alphaNormalize]

example (model : LabelAlphaModel) : (source.alphaNormalize model).WellFormed :=
  sourceWellFormed model
example (model : LabelAlphaModel) : (checkAlpha source model).isOk = true := by
  unfold checkAlpha
  rw [dif_pos (sourceWellFormed model)]
  rfl

private def duplicateSource : PreAlphaAst Nat Unit Nat String :=
  ⟨.local minted.token, [block, block]⟩

private theorem duplicateNotWellFormed (model : LabelAlphaModel) :
    ¬(duplicateSource.alphaNormalize model).WellFormed := by
  simp [duplicateSource, block, Ast.WellFormed, Ast.toGraph,
    CFG.Graph.WellFormed, CFG.Graph.wellFormed, CFG.Graph.blockIds,
    PreAlphaAst.alphaNormalize, PreAlphaBlock.alphaNormalize]

example (model : LabelAlphaModel) :
    (checkAlpha duplicateSource model).map (fun _ => ()) =
      .error ⟨model.toBlock minted.token.id,
        [model.toBlock minted.token.id, model.toBlock minted.token.id], []⟩ := by
  unfold checkAlpha
  rw [dif_neg (duplicateNotWellFormed model)]
  simp [duplicateSource, block, Ast.blockIds, Ast.toGraph,
    CFG.Graph.unresolvedTargets, CFG.Graph.directTargets, CFG.Graph.findBlock?,
    PreAlphaAst.alphaNormalize, PreAlphaBlock.alphaNormalize,
    PreAlphaEdge.alphaNormalize, PreAlphaTarget.alphaNormalize]
  rfl

end Grass.Tests.Construct.SourceAlpha
