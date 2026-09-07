import Grass.Construct.Source.ConstructionElaborate

/-!
# Unified construction-source elaboration fixtures

Fixtures exercise one generated call instruction through all executable gates,
pin alpha-before-constructor-before-call failure priority, and retain separate
typed-constructor and predicate-bearing call-contract certificates.
-/

namespace Grass.Tests.Construct.SourceConstructionElaborate

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private inductive Terminal where
  | returned
  | failed
deriving Repr, DecidableEq

private inductive Instruction where
  | invoke
  | finish

private def semantics : Semantics Instruction Unit where
  Executes := fun _ _ _ => True

private def effects : EffectModel Instruction Nat where
  derive := List.length

private def blockId (name : String) : BlockId :=
  ⟨⟨"test.source.construction", name⟩⟩
private def exitTag (name : String) : ExitTag :=
  ⟨⟨"test.source.construction", name⟩⟩
private def constructorId : FragmentId :=
  ⟨⟨"test.source.construction", "invoke"⟩⟩
private def missingId : FragmentId :=
  ⟨⟨"test.source.construction", "missing"⟩⟩
private def externalId : ExternalCallId :=
  ⟨⟨"test.source.construction", "provider"⟩⟩

private def provider : CallContract Unit where
  requires := fun _ => True
  entryStack := .empty
  outcomes := [⟨exitTag "normal", .normal, fun _ => True, .empty⟩]

private def call : CallSite Unit Terminal where
  target := .external externalId
  contract := provider
  actualEntryStack := .empty
  returns := [⟨exitTag "normal", .block (blockId "finish")⟩]

private def wrongCall : CallSite Unit Terminal :=
  { call with returns := [⟨exitTag "normal", .terminal .failed⟩] }

private def callModel (selected : CallSite Unit Terminal) :
    ManifestModel Instruction (CallSite Unit Terminal) where
  project
    | .invoke => [selected]
    | .finish => []

private def generatedFragment (_ : Unit) :
    VerifiedFragment semantics effects provider.toBlockContract where
  source := .literal [.invoke]
  contractWellFormed := provider.toBlockContract_wellFormed (by decide)
  effects := 1
  effectsExact := rfl
  localCorrect := by
    intro _ _ _ _
    refine ⟨provider.toBlockContract.exits[0], by simp [CallContract.toBlockContract,
      provider], trivial, ?_⟩
    intro candidate hcandidate _
    simp [CallContract.toBlockContract, provider] at hcandidate
    subst candidate
    rfl

private def generator : Generator Unit Instruction Unit Nat semantics effects where
  contract := fun _ => provider.toBlockContract
  generate := generatedFragment

private def constructor : Constructor Instruction Unit Nat semantics effects where
  id := constructorId
  Parameter := Unit
  generator := generator

private def closure : ConstructorClosure Instruction Unit Nat semantics effects :=
  ⟨[constructor]⟩
private def checkedClosure : CheckedConstructorClosure closure := ⟨by decide⟩

private def finishContract : BlockContract Unit where
  requires := fun _ => True
  exits := [⟨exitTag "done", fun _ => True⟩]

private def entryBody (id : FragmentId) : Source Instruction :=
  .generated id (.literal [.invoke])

private def preEntryBlock (id : FragmentId) :
    PreAlphaBlock Unit Terminal Instruction Unit where
  label := .stable (blockId "entry")
  contract := provider.toBlockContract
  outgoing := [⟨exitTag "normal", .label (.stable (blockId "finish"))⟩]
  body := entryBody id
  annotations := []

private def preFinishBlock : PreAlphaBlock Unit Terminal Instruction Unit where
  label := .stable (blockId "finish")
  contract := finishContract
  outgoing := [⟨exitTag "done", .terminal .returned⟩]
  body := .literal [.finish]
  annotations := []

private def preAst (id : FragmentId) :
    PreAlphaAst Unit Terminal Instruction Unit :=
  ⟨.stable (blockId "entry"), [preEntryBlock id, preFinishBlock]⟩

private def entryBlock : Block Unit Terminal Instruction Unit where
  cfg := ⟨blockId "entry", provider.toBlockContract, call.returnEdges⟩
  body := entryBody constructorId
  annotations := []

private def finishBlock : Block Unit Terminal Instruction Unit where
  cfg := ⟨blockId "finish", finishContract,
    [⟨exitTag "done", .terminal .returned⟩]⟩
  body := .literal [.finish]
  annotations := []

private def ast : Ast Unit Terminal Instruction Unit :=
  ⟨blockId "entry", [entryBlock, finishBlock]⟩

private def input (id : FragmentId) (site : CallSite Unit Terminal) :
    PreAlphaConstructionSource Unit Terminal Instruction Unit Nat
      semantics effects :=
  ⟨preAst id, closure, checkedClosure, callModel site⟩

private def valid := input constructorId call
private def missing := input missingId wrongCall
private def misrouted := input constructorId wrongCall

private def duplicateAst : PreAlphaAst Unit Terminal Instruction Unit :=
  ⟨.stable (blockId "missing"),
    [preEntryBlock missingId, preEntryBlock missingId]⟩

private def duplicate :
    PreAlphaConstructionSource Unit Terminal Instruction Unit Nat
      semantics effects :=
  ⟨duplicateAst, closure, checkedClosure, callModel wrongCall⟩

example (alpha : LabelAlphaModel) :
    (elaborateConstruction valid alpha).isOk = true := rfl
example (alpha : LabelAlphaModel) :
    elaborateConstruction missing alpha =
      .error (.constructors (.unresolved
        [⟨blockId "entry", ⟨missingId, [], []⟩⟩])) := rfl
example (alpha : LabelAlphaModel) :
    elaborateConstruction misrouted alpha =
      .error (.calls (.calls
        [⟨blockId "entry", ⟨[constructorId], [], 0⟩, 0,
          .external externalId, wrongCall.returns⟩])) := rfl
example (alpha : LabelAlphaModel) :
    elaborateConstruction duplicate alpha =
      .error (.alpha ⟨blockId "missing",
        [blockId "entry", blockId "entry"],
        [blockId "finish", blockId "finish"]⟩) := rfl

private def selected : SelectedConstructor closure checkedClosure constructorId :=
  ⟨constructor, rfl⟩
private def application : ConstructorApplication selected := ⟨()⟩

private theorem constructorExact (alpha : LabelAlphaModel) :
    (valid.constructorSource.normalized alpha).Exact := by
  intro located hlocated
  have hnodes : (valid.constructorSource.normalized alpha).ast.constructorNodes =
      [⟨blockId "entry",
        ⟨⟨constructorId, [], []⟩, .literal [.invoke]⟩⟩] := rfl
  rw [hnodes] at hlocated
  simp only [List.mem_singleton] at hlocated
  subst located
  exact ⟨selected, application, rfl⟩

private theorem callExact (alpha : LabelAlphaModel) :
    (valid.callSource.normalized alpha).Exact := by
  intro located hlocated
  have hoccurrences : (valid.callSource.normalized alpha).occurrences =
      [⟨blockId "entry", ⟨[constructorId], [], 0⟩, 0, call⟩] := rfl
  rw [hoccurrences] at hlocated
  simp only [List.mem_singleton] at hlocated
  subst located
  exact ⟨entryBlock, rfl, rfl⟩

private theorem structural (alpha : LabelAlphaModel) :
    (valid.authored.alphaNormalize alpha).WellFormed := by
  change ast.WellFormed
  decide

private theorem constructorsWellFormed (alpha : LabelAlphaModel) :
    (valid.constructorSource.normalized alpha).WellFormed := by
  exact ⟨structural alpha, rfl⟩

private theorem callsWellFormed (alpha : LabelAlphaModel) :
    (valid.callSource.normalized alpha).WellFormed := by
  change (AuthoredCallSource.mk ast (callModel call)).WellFormed
  decide

private def checked (alpha : LabelAlphaModel) :
    ConstructionElaborated valid alpha := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨valid.authored.alphaNormalize alpha,
      (valid.authored.alphaNormalize alpha).manifest,
      rfl, rfl, structural alpha⟩
  · exact ⟨constructorsWellFormed alpha⟩
  · exact ⟨callsWellFormed alpha⟩

private def certified (alpha : LabelAlphaModel) :
    CertifiedConstructionElaborated valid alpha :=
  ⟨checked alpha, constructorExact alpha, callExact alpha⟩

example (alpha : LabelAlphaModel) :
    (valid.constructorSource.normalized alpha).Exact :=
  (certified alpha).constructorApplications
example (alpha : LabelAlphaModel) :
    (valid.callSource.normalized alpha).Exact :=
  (certified alpha).callContracts
example (alpha : LabelAlphaModel) :
    (valid.constructorSource.normalized alpha).ast =
      (valid.callSource.normalized alpha).ast := rfl

end Grass.Tests.Construct.SourceConstructionElaborate
