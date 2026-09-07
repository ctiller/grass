import Grass.Construct.StackScopeSession

/-!
# Generative stack-scope session fixtures

Fixtures pin the single-mint supply transition, token-indexed closure ledger,
exact all-exit coverage, object binding, and rejection of an open exit.
-/

namespace Grass.Tests.Construct.StackScopeSession

open Grass.Core Grass.CFG Grass.Construct Grass.Construct.Layout

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def child : ScopeId := ⟨⟨"child"⟩⟩
private def rootDecl : ScopeDecl := ⟨root, none⟩
private def childDecl : ScopeDecl := ⟨child, some root⟩
private def rootObject : Layout.StackObject profile :=
  ⟨⟨"root.value"⟩, ⟨8, 8⟩, 0, root⟩
private def childObject : Layout.StackObject profile :=
  ⟨⟨"child.value"⟩, ⟨8, 8⟩, 8, child⟩
private def layout : StackLayout profile :=
  ⟨[rootDecl, childDecl], [rootObject, childObject], 16, 8, 64⟩
private def checked : CheckedStackLayout profile := ⟨layout, by decide⟩
private def rootRef : StackScopeRef checked := ⟨rootDecl, by decide⟩
private def rootSlot : StackObjectRef checked := ⟨rootObject, by decide⟩
private def childSlot : StackObjectRef checked := ⟨childObject, by decide⟩

private def tag (name : String) : ExitTag := ⟨⟨"test.stack.session", name⟩⟩
private def normal : ExitTag := tag "normal"
private def fault : ExitTag := tag "fault"
private def contract : BlockContract Unit :=
  ⟨fun _ => True, [⟨normal, fun _ => True⟩, ⟨fault, fun _ => True⟩]⟩

private def closed (id : StackScopeId) :
    ScopeExit (StackScopeResource id String) :=
  ⟨[], [], []⟩
private def validLedger (id : StackScopeId) :
    StackScopeLedger contract (StackScopeResource id String) :=
  ⟨[⟨normal, closed id⟩, ⟨fault, closed id⟩]⟩

private def supply : StackScopeSupply := FreshSupply.initial
private def minted : MintedStackScope supply checked := supply.mint checked rootRef
private def checkedClosure : CheckedStackScope (contract := contract)
    (Resource := StackScopeResource minted.token.id String) :=
  ⟨validLedger minted.token.id, by decide⟩
private def session : StackScopeSession supply checked contract String :=
  ⟨minted, checkedClosure⟩

example : ¬supply.Issued session.token.id := session.freshBefore
example : session.after.Issued session.token.id := session.issuedAfter
example : session.token.id = supply.fresh.1 := session.tokenExact
example : session.after = supply.fresh.2 := session.afterExact
example : session.after.fresh.1 ≠ session.token.id :=
  session.neverReissued (.refl session.after)
example : session.closure.ledger.exitTags = contract.exitTags :=
  session.exitTagsExact
example (exit : StackScopeExit (StackScopeResource session.token.id String))
    (member : exit ∈ session.closure.ledger.exits) : exit.resources.WellFormed :=
  session.exitClosed exit member
example : (session.bindStackObject? rootSlot).isSome = true := by decide
example : session.bindStackObject? childSlot = none := by rfl
example : (checkStackScopeSession supply checked rootRef contract String validLedger).isOk =
    true := by decide

private def openLedger (id : StackScopeId) :
    StackScopeLedger contract (StackScopeResource id String) :=
  ⟨[⟨normal, ⟨[], [⟨"loan"⟩], []⟩⟩, ⟨fault, closed id⟩]⟩

example : (checkStackScopeSession supply checked rootRef contract String openLedger).map
    (fun _ => ()) = .error (.openExit normal) := by rfl

end Grass.Tests.Construct.StackScopeSession
