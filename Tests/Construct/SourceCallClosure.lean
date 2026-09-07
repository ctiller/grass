import Grass.Construct.Source.CallElaborate

/-!
# Authored call-closure fixtures

Fixtures derive a call from one instruction, accept its exact containing-block
route, reject a different but otherwise resolved route, and retain separate
proof authority for equality of block and call contracts.
-/

namespace Grass.Tests.Construct.SourceCallClosure

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

private inductive Terminal where
  | returned
  | failed
deriving Repr, DecidableEq

private inductive Instruction where
  | invoke
  | finish

private def blockId (name : String) : BlockId :=
  ⟨⟨"test.source.call", name⟩⟩
private def exitTag (name : String) : ExitTag :=
  ⟨⟨"test.source.call", name⟩⟩
private def externalId : ExternalCallId :=
  ⟨⟨"test.source.call", "provider"⟩⟩

private def provider : CallContract Unit where
  requires := fun _ => True
  entryStack := .empty
  outcomes := [⟨exitTag "normal", .normal, fun _ => True, .empty⟩]

private def call : CallSite Unit Terminal where
  target := .external externalId
  contract := provider
  actualEntryStack := .empty
  returns := [⟨exitTag "normal", .block (blockId "finish")⟩]

private def wrongRoute : CallSite Unit Terminal :=
  { call with returns := [⟨exitTag "normal", .terminal .failed⟩] }

private def finishContract : BlockContract Unit where
  requires := fun _ => True
  exits := [⟨exitTag "done", fun _ => True⟩]

private def entryBlock : Block Unit Terminal Instruction Unit where
  cfg := ⟨blockId "entry", provider.toBlockContract, call.returnEdges⟩
  body := .literal [.invoke]
  annotations := []

private def finishBlock : Block Unit Terminal Instruction Unit where
  cfg := ⟨blockId "finish", finishContract,
    [⟨exitTag "done", .terminal .returned⟩]⟩
  body := .literal [.finish]
  annotations := []

private def ast : Ast Unit Terminal Instruction Unit :=
  ⟨blockId "entry", [entryBlock, finishBlock]⟩

private def model (site : CallSite Unit Terminal) :
    ManifestModel Instruction (CallSite Unit Terminal) where
  project
    | .invoke => [site]
    | .finish => []

private def source : AuthoredCallSource Unit Terminal Instruction Unit :=
  ⟨ast, model call⟩

private def misrouted : AuthoredCallSource Unit Terminal Instruction Unit :=
  ⟨ast, model wrongRoute⟩

private def nonTailAst : Ast Unit Terminal Instruction Unit :=
  ⟨blockId "entry",
    [{ entryBlock with body := .literal [.invoke, .finish] }, finishBlock]⟩

private def nonTail : AuthoredCallSource Unit Terminal Instruction Unit :=
  ⟨nonTailAst, model call⟩

private def duplicateModel :
    ManifestModel Instruction (CallSite Unit Terminal) where
  project
    | .invoke => [call, call]
    | .finish => []

private def duplicateProjection :
    AuthoredCallSource Unit Terminal Instruction Unit :=
  ⟨ast, duplicateModel⟩

private def preEntryBlock : PreAlphaBlock Unit Terminal Instruction Unit where
  label := .stable (blockId "entry")
  contract := provider.toBlockContract
  outgoing := [⟨exitTag "normal", .label (.stable (blockId "finish"))⟩]
  body := .literal [.invoke]
  annotations := []

private def preFinishBlock : PreAlphaBlock Unit Terminal Instruction Unit where
  label := .stable (blockId "finish")
  contract := finishContract
  outgoing := [⟨exitTag "done", .terminal .returned⟩]
  body := .literal [.finish]
  annotations := []

private def preAst : PreAlphaAst Unit Terminal Instruction Unit :=
  ⟨.stable (blockId "entry"), [preEntryBlock, preFinishBlock]⟩

private def preSource : PreAlphaCallSource Unit Terminal Instruction Unit :=
  ⟨preAst, model call⟩

private def preMisrouted : PreAlphaCallSource Unit Terminal Instruction Unit :=
  ⟨preAst, model wrongRoute⟩

private def duplicatePreAst : PreAlphaAst Unit Terminal Instruction Unit :=
  ⟨.stable (blockId "missing"), [preEntryBlock, preEntryBlock]⟩

private def duplicatePreSource :
    PreAlphaCallSource Unit Terminal Instruction Unit :=
  ⟨duplicatePreAst, model wrongRoute⟩

example : ast.WellFormed := by decide
example : source.occurrences.length = 1 := rfl
example : source.occurrences.map (fun located => located.item.target) =
    [.external externalId] := rfl
example : source.WellFormed := by decide
example : (checkAuthoredCalls source).isOk = true := rfl
example : source.unclosed = [] := source.unclosed_eq_nil (by decide)

private theorem exact : source.Exact := by
  intro located hlocated
  have hoccurrences : source.occurrences =
      [⟨blockId "entry", ⟨[], [], 0⟩, 0, call⟩] := rfl
  rw [hoccurrences] at hlocated
  simp only [List.mem_singleton] at hlocated
  subst located
  exact ⟨entryBlock, rfl, rfl⟩

private def certified : CertifiedAuthoredCallSource source :=
  ⟨⟨by decide⟩, exact⟩

example : source.Exact := certified.exact
example : ¬misrouted.WellFormed := by decide
example : (checkAuthoredCalls misrouted).isOk = false := rfl
example : misrouted.unclosed =
    [⟨blockId "entry", ⟨[], [], 0⟩, 0,
      .external externalId, wrongRoute.returns⟩] := rfl
example : nonTail.ast.WellFormed := by decide
example : ¬nonTail.WellFormed := by decide
example : (checkAuthoredCalls nonTail).isOk = false := rfl
example : ¬duplicateProjection.WellFormed := by decide
example : (checkAuthoredCalls duplicateProjection).isOk = false := rfl

example (alpha : LabelAlphaModel) :
    preSource.normalized alpha = source := rfl
example (alpha : LabelAlphaModel) :
    (elaborateCalls preSource alpha).isOk = true := rfl
example (alpha : LabelAlphaModel) :
    (elaborateCalls preMisrouted alpha).isOk = false := rfl
example (alpha : LabelAlphaModel) :
    (elaborateCalls duplicatePreSource alpha).isOk = false := rfl
example (alpha : LabelAlphaModel) :
    elaborateCalls duplicatePreSource alpha =
      .error (.alpha ⟨blockId "missing",
        [blockId "entry", blockId "entry"],
        [blockId "finish", blockId "finish"]⟩) := rfl

private theorem preWellFormed (alpha : LabelAlphaModel) :
    (preAst.alphaNormalize alpha).WellFormed := by
  change ast.WellFormed
  decide

private def callElaborated (alpha : LabelAlphaModel) :
    CallElaborated preSource alpha := by
  have hnormalized : preSource.normalized alpha = source := rfl
  refine ⟨?_, ?_⟩
  · exact ⟨preAst.alphaNormalize alpha,
      (preAst.alphaNormalize alpha).manifest, rfl, rfl, preWellFormed alpha⟩
  · rw [hnormalized]
    exact ⟨by decide⟩

private def callCertified (alpha : LabelAlphaModel) :
    CertifiedCallElaborated preSource alpha := by
  have hnormalized : preSource.normalized alpha = source := rfl
  refine ⟨callElaborated alpha, ?_⟩
  rw [hnormalized]
  exact exact

example (alpha : LabelAlphaModel) :
    (preSource.normalized alpha).unclosed = [] :=
  (callElaborated alpha).unclosed_eq_nil
example (alpha : LabelAlphaModel) :
    (preSource.normalized alpha).Exact :=
  (callCertified alpha).exact

end Grass.Tests.Construct.SourceCallClosure
