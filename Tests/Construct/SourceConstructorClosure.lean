import Grass.Construct.Source.ConstructorClosure

/-!
# Authored constructor-closure fixtures

Fixtures cover exact structural occurrence locations, successful checked
closure, a missing zero-instruction nested constructor, and structural failure
ordering before constructor diagnostics.
-/

namespace Grass.Tests.Construct.SourceConstructorClosure

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private inductive Instruction where
  | emit (value : Nat)
deriving Repr, DecidableEq

private def semantics : Semantics Instruction Unit where
  Executes := fun _ _ _ => True

private def effects : EffectModel Instruction Nat where
  derive := List.length

private def blockId : BlockId := ⟨⟨"test.source.registry", "entry"⟩⟩
private def missingBlockId : BlockId := ⟨⟨"test.source.registry", "missing"⟩⟩
private def exitTag : ExitTag := ⟨⟨"test.source.registry", "done"⟩⟩
private def knownId : FragmentId := ⟨⟨"test.source.registry", "known"⟩⟩
private def missingId : FragmentId := ⟨⟨"test.source.registry", "missing"⟩⟩

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

private def cfgContract : BlockContract Unit := contract 0

private def block (body : Grass.Construct.Fragment.Source Instruction) :
    Grass.Construct.Source.Block Unit Unit Instruction Unit where
  cfg := ⟨blockId, cfgContract, [⟨exitTag, .terminal ()⟩]⟩
  body := body
  annotations := []

private def ast (body : Grass.Construct.Fragment.Source Instruction) :
    Ast Unit Unit Instruction Unit :=
  ⟨blockId, [block body]⟩

private def valid : ConstructorSource Unit Unit Instruction Unit Nat semantics effects :=
  ⟨ast (.generated knownId (.literal [.emit 7])), closure, checkedClosure⟩

private def selected : SelectedConstructor closure checkedClosure knownId :=
  ⟨constructor, rfl⟩
private def application : ConstructorApplication selected := by
  refine ⟨?_⟩
  change Nat
  exact 7

example : valid.ast.constructorOccurrences =
    [⟨blockId, ⟨knownId, [], []⟩⟩] := rfl
example : valid.ast.constructorNodes =
    [⟨blockId, ⟨⟨knownId, [], []⟩, .literal [.emit 7]⟩⟩] := rfl
example : valid.availableIds = [knownId] := rfl
example : valid.unresolved = [] := rfl
example : valid.WellFormed := by native_decide
example : (checkConstructorSource valid).isOk = true := by native_decide

private theorem validExact : valid.Exact := by
  intro located hlocated
  have hnodes : valid.ast.constructorNodes =
      [⟨blockId, ⟨⟨knownId, [], []⟩, .literal [.emit 7]⟩⟩] := rfl
  rw [hnodes] at hlocated
  simp only [List.mem_singleton] at hlocated
  subst located
  exact ⟨selected, application, rfl⟩

private theorem validWellFormed : valid.WellFormed := by
  constructor
  · simp [valid, ast, block, cfgContract, contract, Ast.WellFormed,
      Ast.toGraph, CFG.Graph.WellFormed, CFG.Graph.wellFormed,
      CFG.Graph.blockIds, CFG.Graph.findBlock?, CFG.Graph.outgoingTags,
      CFG.Graph.outgoingUnique, CFG.Graph.edgesDeclared,
      CFG.Graph.exitsCovered, CFG.Graph.targetsResolved,
      BlockContract.wellFormed, BlockContract.exitTags,
      BlockContract.declaresExit]
  · rfl

private def certified : CertifiedConstructorSource valid :=
  ⟨⟨validWellFormed⟩, validExact⟩
example : valid.Exact := certified.exact

private def missingEmpty :
    ConstructorSource Unit Unit Instruction Unit Nat semantics effects :=
  ⟨ast (.generated knownId (.generated missingId .empty)),
    closure, checkedClosure⟩

example : missingEmpty.ast.constructorOccurrences = [
    ⟨blockId, ⟨knownId, [], []⟩⟩,
    ⟨blockId, ⟨missingId, [knownId], []⟩⟩
  ] := rfl
example : missingEmpty.unresolved =
    [⟨blockId, ⟨missingId, [knownId], []⟩⟩] := by native_decide
example : ¬missingEmpty.WellFormed := by native_decide
example : (checkConstructorSource missingEmpty).isOk = false := by native_decide

private def structurallyInvalid :
    ConstructorSource Unit Unit Instruction Unit Nat semantics effects :=
  ⟨⟨missingBlockId, [block (.generated missingId .empty)]⟩,
    closure, checkedClosure⟩

example : ¬structurallyInvalid.ast.WellFormed := by native_decide
example : (checkConstructorSource structurallyInvalid).isOk = false := by native_decide
example : checkConstructorSource structurallyInvalid =
    .error (.structural missingBlockId [blockId]) := rfl

end Grass.Tests.Construct.SourceConstructorClosure
