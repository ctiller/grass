import Grass.Construct.StackScopeCFG

/-!
# CFG stack-scope boundary fixtures

Fixtures pin injective layout-to-CFG scope identity, exact shape entry/LIFO
restoration, all-exit resource closure, and invalid/reopened-shape rejection.
-/

namespace Grass.Tests.Construct.StackScopeCFG

open Grass.Core Grass.CFG Grass.Construct Grass.Construct.Layout

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def rootDecl : ScopeDecl := ⟨root, none⟩
private def layout : StackLayout profile := ⟨[rootDecl], [], 0, 8, 64⟩
private def checked : CheckedStackLayout profile := ⟨layout, by decide⟩
private def rootRef : StackScopeRef checked := ⟨rootDecl, by decide⟩

private def tag : ExitTag := ⟨⟨"test.stack.cfg", "normal"⟩⟩
private def contract : BlockContract Unit :=
  ⟨fun _ => True, [⟨tag, fun _ => True⟩]⟩
private def closedExit (id : Grass.Construct.StackScopeId) :
    StackScopeExit (StackScopeResource id String) :=
  ⟨tag, ⟨[], [], []⟩⟩
private def ledger (id : Grass.Construct.StackScopeId) :
    StackScopeLedger contract (StackScopeResource id String) :=
  ⟨[closedExit id]⟩
private def supply : StackScopeSupply := FreshSupply.initial
private def session : StackScopeSession supply checked contract String :=
  ⟨supply.mint checked rootRef, ⟨ledger supply.fresh.1, by rfl⟩⟩

private def idModel : StackScopeIdModel where
  toCFG := fun scope => ⟨⟨"test.stack.cfg", scope.id.text⟩⟩
  injective := by
    intro left right equal
    have textEqual : left.id.text = right.id.text :=
      congrArg (fun id => id.id.localName) equal
    have nameEqual : left.id = right.id :=
      Grass.Core.Name.eq_of_text_eq textEqual
    cases left
    cases right
    cases nameEqual
    rfl

private def cfgScope : Grass.CFG.StackScopeId := idModel.toCFG root
private def before : StackShape := ⟨32, []⟩
private def boundary : StackScopeBoundary idModel session before :=
  ⟨⟨32, [cfgScope]⟩, by decide, by rfl⟩

example : boundary.entered = ⟨32, [cfgScope]⟩ := rfl
example : boundary.scopeId ∉ before.openScopes := boundary.scopeNotOpenBefore
example : boundary.entered.depth = before.depth := boundary.enteredDepthExact
example : boundary.entered.openScopes = boundary.scopeId :: before.openScopes :=
  boundary.enteredScopesExact
example : boundary.entered.WellFormed := boundary.enteredValid
example : boundary.entered.leaveScope? boundary.scopeId = some before :=
  boundary.leaveExact
example : (checkStackScopeBoundary idModel session before).isOk = true := by decide
example (exit : StackScopeExit (StackScopeResource session.token.id String))
    (member : exit ∈ session.closure.ledger.exits) :
    exit.resources.WellFormed ∧
      boundary.entered.leaveScope? boundary.scopeId = some before :=
  boundary.closesExit exit member

private def reopened : StackShape := ⟨32, [cfgScope]⟩
example : (checkStackScopeBoundary idModel session reopened).map (fun _ => ()) =
    .error (.scopeAlreadyOpen cfgScope) := by rfl

private def invalid : StackShape := ⟨32, [cfgScope, cfgScope]⟩
example : (checkStackScopeBoundary idModel session invalid).map (fun _ => ()) =
    .error .invalidBefore := by rfl

end Grass.Tests.Construct.StackScopeCFG
