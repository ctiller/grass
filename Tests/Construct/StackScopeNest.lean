import Grass.Construct.StackScopeNest

/-!
# Nested generative stack-scope fixtures

Fixtures pin exact two-mint reachability, token distinction, both all-exit
certificates, and staged rejection when the inner ledger remains open.
-/

namespace Grass.Tests.Construct.StackScopeNest

open Grass.Core Grass.CFG Grass.Construct Grass.Construct.Layout

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8⟩
private def outerScope : ScopeId := ⟨⟨"outer"⟩⟩
private def innerScope : ScopeId := ⟨⟨"inner"⟩⟩
private def outerDecl : ScopeDecl := ⟨outerScope, none⟩
private def innerDecl : ScopeDecl := ⟨innerScope, some outerScope⟩
private def layout : StackLayout profile :=
  ⟨[outerDecl, innerDecl], [], 0, 8, 64⟩
private def checked : CheckedStackLayout profile := ⟨layout, by decide⟩
private def outerRef : StackScopeRef checked := ⟨outerDecl, by decide⟩
private def innerRef : StackScopeRef checked := ⟨innerDecl, by decide⟩

private def tag (name : String) : ExitTag := ⟨⟨"test.stack.nest", name⟩⟩
private def normal : ExitTag := tag "normal"
private def fault : ExitTag := tag "fault"
private def contract : BlockContract Unit :=
  ⟨fun _ => True, [⟨normal, fun _ => True⟩, ⟨fault, fun _ => True⟩]⟩

private structure InnerPayload (outer : StackScopeId) where
  owner : StackScopeId
  ownerExact : owner = outer

private def closed {Resource : Type} : ScopeExit Resource := ⟨[], [], []⟩
private def outerLedger (id : StackScopeId) :
    StackScopeLedger contract (StackScopeResource id String) :=
  ⟨[⟨normal, closed⟩, ⟨fault, closed⟩]⟩
private def innerLedger (outerId innerId : StackScopeId) :
    StackScopeLedger contract (StackScopeResource innerId (InnerPayload outerId)) :=
  ⟨[⟨normal, closed⟩, ⟨fault, closed⟩]⟩

private def supply : StackScopeSupply := FreshSupply.initial
private def outer : StackScopeSession supply checked contract String :=
  ⟨supply.mint checked outerRef, ⟨outerLedger supply.fresh.1, by rfl⟩⟩
private def inner : StackScopeSession outer.after checked contract
    (InnerPayload outer.token.id) :=
  ⟨outer.after.mint checked innerRef,
    ⟨innerLedger outer.token.id outer.after.fresh.1, by rfl⟩⟩
private def nest : StackScopeNest supply checked checked contract contract String InnerPayload :=
  ⟨outer, inner⟩

example : FreshSupply.Reachable supply nest.outer.after := nest.beforeToOuter
example : FreshSupply.Reachable nest.outer.after nest.inner.after := nest.outerToInner
example : FreshSupply.Reachable supply nest.inner.after := nest.beforeToInner
example : nest.inner.after.Issued nest.outer.token.id := nest.outerIssuedAfterInner
example : nest.inner.token.id ≠ nest.outer.token.id := nest.innerTokenDistinct
example : nest.outer.closure.ledger.exitTags = contract.exitTags :=
  nest.outer.exitTagsExact
example : nest.inner.closure.ledger.exitTags = contract.exitTags :=
  nest.inner.exitTagsExact
example : (checkStackScopeNest supply checked checked outerRef innerRef contract contract
    String InnerPayload outerLedger innerLedger).isOk = true := by decide

private def openInnerLedger (outerId innerId : StackScopeId) :
    StackScopeLedger contract (StackScopeResource innerId (InnerPayload outerId)) :=
  ⟨[⟨normal, closed⟩,
    ⟨fault, ⟨[], [], [⟨outerId, rfl⟩]⟩⟩]⟩

example : (checkStackScopeNest supply checked checked outerRef innerRef contract contract
    String InnerPayload outerLedger openInnerLedger).map (fun _ => ()) =
    .error (.inner (.openExit fault)) := by rfl

end Grass.Tests.Construct.StackScopeNest
