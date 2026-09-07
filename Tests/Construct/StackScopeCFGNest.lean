import Grass.Construct.StackScopeCFGNest

/-!
# Nested CFG stack-scope boundary fixtures

Fixtures pin two-level scope entry, identity distinction, exact LIFO
restoration, all-exit closure, and staged outer/inner rejection.
-/

namespace Grass.Tests.Construct.StackScopeCFGNest

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

private def tag : ExitTag := ⟨⟨"test.stack.cfg.nest", "normal"⟩⟩
private def contract : BlockContract Unit :=
  ⟨fun _ => True, [⟨tag, fun _ => True⟩]⟩
private structure InnerPayload (outer : Grass.Construct.StackScopeId) where
  owner : Grass.Construct.StackScopeId
  ownerExact : owner = outer
private def closed {Resource : Type} : ScopeExit Resource := ⟨[], [], []⟩
private def outerLedger (id : Grass.Construct.StackScopeId) :
    StackScopeLedger contract (StackScopeResource id String) :=
  ⟨[⟨tag, closed⟩]⟩
private def innerLedger (outerId innerId : Grass.Construct.StackScopeId) :
    StackScopeLedger contract (StackScopeResource innerId (InnerPayload outerId)) :=
  ⟨[⟨tag, closed⟩]⟩

private def supply : StackScopeSupply := FreshSupply.initial
private def outer : StackScopeSession supply checked contract String :=
  ⟨supply.mint checked outerRef, ⟨outerLedger supply.fresh.1, by rfl⟩⟩
private def inner : StackScopeSession outer.after checked contract
    (InnerPayload outer.token.id) :=
  ⟨outer.after.mint checked innerRef,
    ⟨innerLedger outer.token.id outer.after.fresh.1, by rfl⟩⟩
private def nest : StackScopeNest supply checked checked contract contract
    String InnerPayload :=
  ⟨outer, inner, rfl⟩

private def idModel : StackScopeIdModel where
  toCFG := fun scope => ⟨⟨"test.stack.cfg.nest", scope.id.text⟩⟩
  injective := by
    intro left right equal
    have textEqual : left.id.text = right.id.text :=
      congrArg (fun id => id.id.localName) equal
    have nameEqual : left.id = right.id := Grass.Core.Name.eq_of_text_eq textEqual
    cases left
    cases right
    cases nameEqual
    rfl

private def outerCFG : Grass.CFG.StackScopeId := idModel.toCFG outerScope
private def innerCFG : Grass.CFG.StackScopeId := idModel.toCFG innerScope
private def before : StackShape := ⟨48, []⟩
private def outerBoundary : StackScopeBoundary idModel nest.outer before :=
  ⟨⟨48, [outerCFG]⟩, by decide, by rfl⟩
private def innerBoundary :
    StackScopeBoundary idModel nest.inner outerBoundary.entered :=
  ⟨⟨48, [innerCFG, outerCFG]⟩, by decide, by rfl⟩
private def boundary : StackScopeNestBoundary idModel nest before :=
  ⟨outerBoundary, innerBoundary⟩

example : boundary.inner.scopeId ≠ boundary.outer.scopeId :=
  boundary.scopeIdsDistinct
example : boundary.inner.entered.openScopes = [innerCFG, outerCFG] :=
  boundary.enteredScopesExact
example : boundary.inner.entered.depth = before.depth := boundary.enteredDepthExact
example : boundary.inner.entered.WellFormed := boundary.enteredValid
example :
    boundary.inner.entered.leaveScope? boundary.inner.scopeId =
        some boundary.outer.entered ∧
      boundary.outer.entered.leaveScope? boundary.outer.scopeId = some before :=
  boundary.leaveBothExact
example : (checkStackScopeNestBoundary idModel nest before).isOk = true := by decide

example
    (outerExit : StackScopeExit
      (StackScopeResource nest.outer.token.id String))
    (outerMember : outerExit ∈ nest.outer.closure.ledger.exits)
    (innerExit : StackScopeExit
      (StackScopeResource nest.inner.token.id
        (InnerPayload nest.outer.token.id)))
    (innerMember : innerExit ∈ nest.inner.closure.ledger.exits) :
    outerExit.resources.WellFormed ∧ innerExit.resources.WellFormed ∧
      boundary.inner.entered.leaveScope? boundary.inner.scopeId =
        some boundary.outer.entered ∧
      boundary.outer.entered.leaveScope? boundary.outer.scopeId = some before :=
  boundary.closesExits outerExit outerMember innerExit innerMember

private def outerReopened : StackShape := ⟨48, [outerCFG]⟩
example : (checkStackScopeNestBoundary idModel nest outerReopened).map (fun _ => ()) =
    .error (.outer (.scopeAlreadyOpen outerCFG)) := by rfl

private def innerReopened : StackShape := ⟨48, [innerCFG]⟩
example : (checkStackScopeNestBoundary idModel nest innerReopened).map (fun _ => ()) =
    .error (.inner (.scopeAlreadyOpen innerCFG)) := by rfl

end Grass.Tests.Construct.StackScopeCFGNest
