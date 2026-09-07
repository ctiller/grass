import Grass.Construct.StackScopeToken

/-!
# Generative lexical stack-scope token fixtures

Fixtures pin fresh-supply advancement, issue-state transition, and exact scope
matching for checked stack objects.
-/

namespace Grass.Tests.Construct.StackScopeToken

open Grass.Core Grass.Construct Grass.Construct.Layout

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
private def supply : StackScopeSupply := FreshSupply.initial
private def minted : MintedStackScope supply checked := supply.mint checked rootRef

example : ¬supply.Issued minted.token.id := minted.freshBefore
example : minted.after.Issued minted.token.id := minted.issuedAfter
example : minted.after.fresh.1 ≠ minted.token.id :=
  minted.neverReissued (.refl minted.after)
example : minted.token.scopeRef.scope = rootDecl := rfl
example : (bindStackObject? minted.token rootSlot).isSome = true := by decide
example : bindStackObject? minted.token childSlot = none := by rfl

private def bound : ScopedStackObject minted.token :=
  ⟨rootSlot, rfl⟩
example : bound.slot.object.scope = minted.token.scopeRef.scope.id := bound.scopeExact

end Grass.Tests.Construct.StackScopeToken
