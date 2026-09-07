import Grass.Construct.Source.ConstructorLower

/-!
# Verified constructor-aware lowering fixtures

The fixture supplies constructor exactness and semantic block verification as
separate values over one normalized source, then pins total lowering back to
the original pre-alpha instruction list.
-/

namespace Grass.Tests.Construct.SourceConstructorLower

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private inductive Instruction where
  | emit (value : Nat)
deriving Repr, DecidableEq

private def semantics : Semantics Instruction Unit where
  Executes := fun _ _ _ => True

private def effects : EffectModel Instruction Nat where
  derive := List.length

private def blockId : BlockId := ⟨⟨"test.source.lower", "entry"⟩⟩
private def exitTag : ExitTag := ⟨⟨"test.source.lower", "done"⟩⟩
private def constructorId : FragmentId :=
  ⟨⟨"test.source.lower", "emit"⟩⟩

private def contract : BlockContract Unit where
  requires := fun _ => True
  exits := [⟨exitTag, fun _ => True⟩]

private theorem locallyCorrect
    (instructions : List Instruction) :
    ∀ before after,
      contract.requires before →
      semantics.Executes instructions before after →
      ClassifiesExactlyOneExit contract after := by
  intro _ _ _ _
  refine ⟨⟨exitTag, fun _ => True⟩, by simp [contract], trivial, ?_⟩
  intro candidate hcandidate _
  simp [contract] at hcandidate
  subst candidate
  rfl

private def generatedFragment (value : Nat) :
    VerifiedFragment semantics effects contract where
  source := .literal [.emit value]
  contractWellFormed := by
    simp [contract, BlockContract.WellFormed, BlockContract.wellFormed,
      BlockContract.exitTags]
  effects := 1
  effectsExact := rfl
  localCorrect := locallyCorrect _

private def generator : Generator Nat Instruction Unit Nat semantics effects where
  contract := fun _ => contract
  generate := generatedFragment

private def constructor : Constructor Instruction Unit Nat semantics effects where
  id := constructorId
  Parameter := Nat
  generator := generator

private def body : Grass.Construct.Fragment.Source Instruction :=
  .generated constructorId (.literal [.emit 7])

private def preBlock : PreAlphaBlock Unit Unit Instruction Unit :=
  ⟨.stable blockId, contract, [⟨exitTag, .terminal ()⟩], body, []⟩

private def authored : PreAlphaAst Unit Unit Instruction Unit :=
  ⟨.stable blockId, [preBlock]⟩

private def closure : ConstructorClosure Instruction Unit Nat semantics effects :=
  ⟨[constructor]⟩

private def checkedClosure : CheckedConstructorClosure closure := ⟨by decide⟩

private def selected : SelectedConstructor closure checkedClosure constructorId :=
  ⟨constructor, rfl⟩

private def application : ConstructorApplication selected := by
  refine ⟨?_⟩
  change Nat
  exact 7

private def source :
    PreAlphaConstructorSource Unit Unit Instruction Unit Nat semantics effects :=
  ⟨authored, closure, checkedClosure⟩

private theorem authoredWellFormed (model : LabelAlphaModel) :
    (authored.alphaNormalize model).WellFormed := by
  simp [authored, preBlock, contract, Ast.WellFormed, Ast.toGraph,
    CFG.Graph.WellFormed, CFG.Graph.wellFormed, CFG.Graph.blockIds,
    CFG.Graph.findBlock?, CFG.Graph.outgoingTags, CFG.Graph.outgoingUnique,
    CFG.Graph.edgesDeclared, CFG.Graph.exitsCovered, CFG.Graph.targetsResolved,
    BlockContract.wellFormed, BlockContract.exitTags,
    BlockContract.declaresExit, PreAlphaAst.alphaNormalize,
    PreAlphaBlock.alphaNormalize, PreAlphaEdge.alphaNormalize,
    PreAlphaTarget.alphaNormalize]

private def elaborated (model : LabelAlphaModel) :
    ElaboratedSource source.authored model :=
  ⟨source.authored.alphaNormalize model,
    (source.authored.alphaNormalize model).manifest,
    rfl, rfl, authoredWellFormed model⟩

private def constructorChecked (model : LabelAlphaModel) :
    CheckedConstructorSource (source.normalized model) :=
  ⟨authoredWellFormed model, rfl⟩

private theorem constructorExact (model : LabelAlphaModel) :
    (source.normalized model).Exact := by
  intro located hlocated
  have hnodes : (source.normalized model).ast.constructorNodes =
      [⟨blockId, ⟨⟨constructorId, [], []⟩, .literal [.emit 7]⟩⟩] := rfl
  rw [hnodes] at hlocated
  simp only [List.mem_singleton] at hlocated
  subst located
  exact ⟨selected, application, rfl⟩

private def constructorCertified (model : LabelAlphaModel) :
    CertifiedConstructorElaborated source model :=
  ⟨⟨elaborated model, constructorChecked model⟩, constructorExact model⟩

private def fragment : VerifiedFragment semantics effects contract where
  source := body
  contractWellFormed := by
    simp [contract, BlockContract.WellFormed, BlockContract.wellFormed,
      BlockContract.exitTags]
  effects := 1
  effectsExact := rfl
  localCorrect := locallyCorrect _

private def verifiedBlock (model : LabelAlphaModel) :
    @VerifiedBlock Unit Unit Instruction Unit Nat semantics effects where
  authored := preBlock.alphaNormalize model
  fragment := fragment
  sourceExact := rfl

private def verifiedAst (model : LabelAlphaModel) :
    VerifiedAst semantics effects (source.authored.alphaNormalize model) where
  structural := authoredWellFormed model
  blocks := [verifiedBlock model]
  blocksExact := rfl

private def checked (model : LabelAlphaModel) :
    VerifiedConstructorElaborated source model :=
  ⟨constructorCertified model, verifiedAst model⟩

example (model : LabelAlphaModel) :
    (checked model).lower.items.map LoweredInstruction.instruction =
      [.emit 7] :=
  (checked model).lower_instructions_exact

example (model : LabelAlphaModel) :
    (checked model).lower.graph = (source.authored.alphaNormalize model).toGraph :=
  (checked model).lower_graph

example (model : LabelAlphaModel) :
    (checked model).lower.items =
      (source.authored.alphaNormalize model).loweredItems :=
  (checked model).lower_items_exact

example (model : LabelAlphaModel) : (source.normalized model).Exact :=
  (checked model).constructorApplicationsExact

end Grass.Tests.Construct.SourceConstructorLower
