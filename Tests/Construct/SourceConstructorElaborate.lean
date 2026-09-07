import Grass.Construct.Source.ConstructorElaborate

/-!
# Constructor-aware elaboration fixtures

Fixtures pin successful alpha/CFG plus constructor closure, exact typed
application certification, constructor rejection after structural success, and
alpha failure precedence over constructor diagnostics.
-/

namespace Grass.Tests.Construct.SourceConstructorElaborate

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private inductive Instruction where
  | emit (value : Nat)
deriving Repr, DecidableEq

private def semantics : Semantics Instruction Unit where
  Executes := fun _ _ _ => True

private def effects : EffectModel Instruction Nat where
  derive := List.length

private def blockId : BlockId := ⟨⟨"test.source.elaborate", "entry"⟩⟩
private def missingBlockId : BlockId := ⟨⟨"test.source.elaborate", "missing"⟩⟩
private def exitTag : ExitTag := ⟨⟨"test.source.elaborate", "done"⟩⟩
private def knownId : FragmentId := ⟨⟨"test.source.elaborate", "known"⟩⟩
private def missingId : FragmentId := ⟨⟨"test.source.elaborate", "missing"⟩⟩

private def contract (_ : Nat) : BlockContract Unit where
  requires := fun _ => True
  exits := [⟨exitTag, fun _ => True⟩]

private def generated (value : Nat) : VerifiedFragment semantics effects (contract value) where
  source := .literal [.emit value]
  contractWellFormed := by
    simp [contract, BlockContract.WellFormed, BlockContract.wellFormed,
      BlockContract.exitTags]
  effects := 1
  effectsExact := rfl
  localCorrect := by
    intro _ _ _ _
    refine ⟨⟨exitTag, fun _ => True⟩, by simp [contract], trivial, ?_⟩
    intro candidate hcandidate _
    simp [contract] at hcandidate
    subst candidate
    rfl

private def generator : Generator Nat Instruction Unit Nat semantics effects where
  contract := contract
  generate := generated

private def constructor : Constructor Instruction Unit Nat semantics effects where
  id := knownId
  Parameter := Nat
  generator := generator

private def closure : ConstructorClosure Instruction Unit Nat semantics effects :=
  ⟨[constructor]⟩
private def checkedClosure : CheckedConstructorClosure closure := ⟨by decide⟩

private def block (body : Grass.Construct.Fragment.Source Instruction) :
    PreAlphaBlock Unit Unit Instruction Unit :=
  ⟨.stable blockId, contract 0, [⟨exitTag, .terminal ()⟩], body, []⟩

private def authored (body : Grass.Construct.Fragment.Source Instruction) :
    PreAlphaAst Unit Unit Instruction Unit :=
  ⟨.stable blockId, [block body]⟩

private def input (body : Grass.Construct.Fragment.Source Instruction) :
    PreAlphaConstructorSource Unit Unit Instruction Unit Nat semantics effects :=
  ⟨authored body, closure, checkedClosure⟩

private def valid := input (.generated knownId (.literal [.emit 7]))

private theorem authoredWellFormed
    (body : Grass.Construct.Fragment.Source Instruction)
    (model : LabelAlphaModel) :
    ((authored body).alphaNormalize model).WellFormed := by
  simp [authored, block, contract, Ast.WellFormed, Ast.toGraph,
    CFG.Graph.WellFormed, CFG.Graph.wellFormed, CFG.Graph.blockIds,
    CFG.Graph.findBlock?, CFG.Graph.outgoingTags, CFG.Graph.outgoingUnique,
    CFG.Graph.edgesDeclared, CFG.Graph.exitsCovered, CFG.Graph.targetsResolved,
    BlockContract.wellFormed, BlockContract.exitTags,
    BlockContract.declaresExit, PreAlphaAst.alphaNormalize,
    PreAlphaBlock.alphaNormalize, PreAlphaEdge.alphaNormalize,
    PreAlphaTarget.alphaNormalize]

private def ordinary (model : LabelAlphaModel) :
    ElaboratedSource valid.authored model :=
  ⟨valid.authored.alphaNormalize model,
    (valid.authored.alphaNormalize model).manifest,
    rfl, rfl, authoredWellFormed _ model⟩

private theorem normalizedWellFormed (model : LabelAlphaModel) :
    (valid.normalized model).WellFormed := by
  exact ⟨authoredWellFormed _ model, rfl⟩

private def result (model : LabelAlphaModel) : ConstructorElaborated valid model :=
  ⟨ordinary model, ⟨normalizedWellFormed model⟩⟩

example (model : LabelAlphaModel) :
    (result model).elaborated.authored = valid.authored.alphaNormalize model := rfl
example (model : LabelAlphaModel) :
    (result model).elaborated.authored = (valid.normalized model).ast :=
  (result model).elaboratedAstExact
example (model : LabelAlphaModel) :
    (valid.normalized model).unresolved = [] :=
  (result model).unresolved_eq_nil
example (model : LabelAlphaModel) :
    (result model).elaborated.manifest.instructionCount = 1 := rfl
example (model : LabelAlphaModel) :
    (result model).elaborated.authored.blocks.flatMap
      (fun authoredBlock => authoredBlock.body.expand) =
      valid.authored.instructions :=
  (result model).instructionsExact
example (model : LabelAlphaModel) :
    (elaborateConstructors valid model).isOk = true := rfl

private def selected : SelectedConstructor closure checkedClosure knownId :=
  ⟨constructor, rfl⟩
private def application : ConstructorApplication selected := by
  refine ⟨?_⟩
  change Nat
  exact 7

private theorem normalizedExact (model : LabelAlphaModel) :
    (valid.normalized model).Exact := by
  intro located hlocated
  have hnodes : (valid.normalized model).ast.constructorNodes =
      [⟨blockId, ⟨⟨knownId, [], []⟩, .literal [.emit 7]⟩⟩] := rfl
  rw [hnodes] at hlocated
  simp only [List.mem_singleton] at hlocated
  subst located
  exact ⟨selected, application, rfl⟩

private def certified (model : LabelAlphaModel) :
    CertifiedConstructorElaborated valid model :=
  ⟨result model, normalizedExact model⟩
example (model : LabelAlphaModel) : (valid.normalized model).Exact :=
  (certified model).exact

private def missing := input (.generated missingId .empty)

example (model : LabelAlphaModel) :
    (missing.normalized model).unresolved =
      [⟨blockId, ⟨missingId, [], []⟩⟩] := rfl
example (model : LabelAlphaModel) :
    (elaborateConstructors missing model).isOk = false := rfl
example (model : LabelAlphaModel) :
    elaborateConstructors missing model =
      .error (.constructors (.unresolved
        [⟨blockId, ⟨missingId, [], []⟩⟩])) := rfl

private def duplicateAuthored : PreAlphaAst Unit Unit Instruction Unit :=
  ⟨.stable missingBlockId,
    [block (.generated missingId .empty), block (.generated missingId .empty)]⟩
private def duplicateInput :
    PreAlphaConstructorSource Unit Unit Instruction Unit Nat semantics effects :=
  ⟨duplicateAuthored, closure, checkedClosure⟩

example (model : LabelAlphaModel) :
    (elaborateConstructors duplicateInput model).isOk = false := rfl
example (model : LabelAlphaModel) :
    elaborateConstructors duplicateInput model =
      .error (.alpha ⟨missingBlockId, [blockId, blockId], []⟩) := rfl

end Grass.Tests.Construct.SourceConstructorElaborate
