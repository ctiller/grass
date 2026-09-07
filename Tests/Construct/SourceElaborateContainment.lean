import Grass.Construct.Source.ElaborateContainment

/-!
# Containment-aware elaboration fixtures

Fixtures pin staged structural/containment checking, exact metadata attachment,
and erasure invariance for the checked result.
-/

namespace Grass.Tests.Construct.SourceElaborateContainment

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private inductive Violation where
  | excessCount
deriving Repr, DecidableEq

private def blockId : BlockId := ⟨⟨"test.elaborate.containment", "entry"⟩⟩
private def tag : ExitTag := ⟨⟨"test.elaborate.containment", "violation"⟩⟩
private def contract : BlockContract Nat :=
  ⟨fun _ => True, [⟨tag, fun _ => True⟩]⟩
private def envelope : AffineReturnEnvelope Int := ⟨0, 1, 4⟩
private def edgeAnnotation : ContainmentAnnotation String Violation Int :=
  ⟨.edge tag (.terminal "violation"), .excessCount, envelope⟩
private def tailAnnotation : ContainmentAnnotation String Violation Int :=
  ⟨.tail ⟨[], [], 1⟩, .excessCount, envelope⟩
private def block : PreAlphaBlock Nat String Nat
    (ContainmentAnnotation String Violation Int) :=
  ⟨.stable blockId, contract, [⟨tag, .terminal "violation"⟩],
    .literal [7, 8], [edgeAnnotation, tailAnnotation]⟩
private def source : PreAlphaAst Nat String Nat
    (ContainmentAnnotation String Violation Int) :=
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

private theorem containmentWellFormed (model : LabelAlphaModel) :
    (source.alphaNormalize model).ContainmentWellFormed := by
  simp [source, block, edgeAnnotation, tailAnnotation, envelope,
    Ast.ContainmentWellFormed, Grass.Construct.Source.Block.containmentWellFormed,
    Grass.Construct.Source.Block.containmentSites, ContainmentSite.attachedTo,
    PreAlphaAst.alphaNormalize, PreAlphaBlock.alphaNormalize]
  constructor
  · rfl
  · native_decide

private def result (model : LabelAlphaModel) :
    ContainmentElaborated source model :=
  let authored := source.alphaNormalize model
  let elaborated : ElaboratedSource source model :=
    ⟨authored, authored.manifest, rfl, rfl, sourceWellFormed model⟩
  ⟨elaborated, containmentWellFormed model⟩

example (model : LabelAlphaModel) :
    (source.alphaNormalize model).ContainmentWellFormed :=
  containmentWellFormed model
example (model : LabelAlphaModel) :
    (elaborateContainment source model).isOk = true := by
  unfold elaborateContainment elaborate checkAlpha
  rw [dif_pos (sourceWellFormed model)]
  rfl
example (model : LabelAlphaModel) :
    ((result model).elaborated.authored.blocks.flatMap fun block =>
      block.body.expand) = source.instructions :=
  (result model).instructionsExact
example (model : LabelAlphaModel) :
    (result model).elaborated.authored.eraseContainment.toGraph =
      (result model).elaborated.authored.toGraph :=
  (result model).erasedGraphExact
example (model : LabelAlphaModel) :
    (result model).elaborated.authored.eraseContainment.expandedBlocks =
      (result model).elaborated.authored.expandedBlocks :=
  (result model).erasedInstructionsExact

private def duplicateBlock : PreAlphaBlock Nat String Nat
    (ContainmentAnnotation String Violation Int) :=
  ⟨.stable blockId, contract, [⟨tag, .terminal "violation"⟩],
    .literal [7, 8], [edgeAnnotation, edgeAnnotation]⟩
private def duplicateSource : PreAlphaAst Nat String Nat
    (ContainmentAnnotation String Violation Int) :=
  ⟨.stable blockId, [duplicateBlock]⟩

private theorem duplicateStructurallyWellFormed (model : LabelAlphaModel) :
    (duplicateSource.alphaNormalize model).WellFormed := by
  simp [duplicateSource, duplicateBlock, contract, tag, Ast.WellFormed,
    Ast.toGraph, CFG.Graph.WellFormed, CFG.Graph.wellFormed,
    CFG.Graph.blockIds, CFG.Graph.findBlock?, CFG.Graph.targetsResolved,
    CFG.Graph.outgoingUnique, CFG.Graph.edgesDeclared, CFG.Graph.exitsCovered,
    CFG.Graph.outgoingTags, BlockContract.wellFormed, BlockContract.exitTags,
    BlockContract.declaresExit, PreAlphaAst.alphaNormalize,
    PreAlphaBlock.alphaNormalize, PreAlphaEdge.alphaNormalize,
    PreAlphaTarget.alphaNormalize]

example (model : LabelAlphaModel) :
    elaborateContainment duplicateSource model =
      .error (.containment (.duplicateSites blockId
        [edgeAnnotation.site, edgeAnnotation.site])) := by
  unfold elaborateContainment elaborate checkAlpha
  rw [dif_pos (duplicateStructurallyWellFormed model)]
  rfl

private def structurallyOpen : PreAlphaAst Nat String Nat
    (ContainmentAnnotation String Violation Int) :=
  ⟨.stable blockId, []⟩
private theorem structurallyOpenInvalid (model : LabelAlphaModel) :
    ¬(structurallyOpen.alphaNormalize model).WellFormed := by
  change ¬(⟨blockId, []⟩ : Ast Nat String Nat
    (ContainmentAnnotation String Violation Int)).WellFormed
  native_decide
example (model : LabelAlphaModel) : elaborateContainment structurallyOpen model =
    .error (.alpha ⟨blockId, [], []⟩) := by
  unfold elaborateContainment elaborate checkAlpha
  rw [dif_neg (structurallyOpenInvalid model)]
  rfl

end Grass.Tests.Construct.SourceElaborateContainment
