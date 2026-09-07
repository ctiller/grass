import Grass.Core.Uid
import Grass.Construct.StackObject

/-!
# Generative lexical stack-scope tokens

`StackScopeSupply.mint` threads the core monotone fresh supply and returns a
token tied to one exact checked layout and declared lexical scope.
`ScopedStackObject` additionally proves that its checked object belongs to that
token's scope. These nominal tokens are construction identities; mapping them
to physical memory provenance remains an execution-model obligation.
-/

namespace Grass.Construct

open Grass.Core Grass.Construct.Layout

/-- Phantom identity domain for lexical stack-scope occurrences. -/
inductive StackScopeTag : Type

/-- Nominal identity of one lexical stack-scope occurrence. -/
abbrev StackScopeId := Uid StackScopeTag

/-- Monotone identity supply for lexical stack-scope occurrences. -/
abbrev StackScopeSupply := FreshSupply StackScopeTag

/-- One declared scope with evidence that it belongs to an exact checked layout. -/
structure StackScopeRef {profile : LayoutProfile}
    (checked : CheckedStackLayout profile) where
  scope : ScopeDecl
  member : scope ∈ checked.layout.scopes

/-- Fresh nominal token for one declared scope in an exact checked layout. -/
structure StackScopeToken {profile : LayoutProfile}
    (checked : CheckedStackLayout profile) where
  id : StackScopeId
  scopeRef : StackScopeRef checked

/-- Result of minting one scope token and advancing its exact input supply. -/
structure MintedStackScope {profile : LayoutProfile}
    (before : StackScopeSupply) (checked : CheckedStackLayout profile) where
  token : StackScopeToken checked
  after : StackScopeSupply
  idExact : token.id = before.fresh.1
  afterExact : after = before.fresh.2

namespace StackScopeSupply

/-- Mint a token for one exact declared scope and advance the supply once. -/
def mint {profile : LayoutProfile} (before : StackScopeSupply)
    (checked : CheckedStackLayout profile) (scopeRef : StackScopeRef checked) :
    MintedStackScope before checked :=
  ⟨⟨before.fresh.1, scopeRef⟩, before.fresh.2, rfl, rfl⟩

end StackScopeSupply

namespace MintedStackScope

variable {profile : LayoutProfile} {before : StackScopeSupply}
  {checked : CheckedStackLayout profile}

/-- A minted scope identity was not issued by its input supply. -/
theorem freshBefore (minted : MintedStackScope before checked) :
    ¬before.Issued minted.token.id := by
  rw [minted.idExact]
  exact FreshSupply.fresh_not_issued before

/-- The advanced supply records the newly minted scope identity. -/
theorem issuedAfter (minted : MintedStackScope before checked) :
    minted.after.Issued minted.token.id := by
  rw [minted.afterExact, minted.idExact]
  exact FreshSupply.issued_fresh before before.fresh.1 |>.mpr (.inr rfl)

/-- No later mint in the same supply history can reissue this scope identity. -/
theorem neverReissued (minted : MintedStackScope before checked)
    {later : StackScopeSupply} (reachable : FreshSupply.Reachable minted.after later) :
    later.fresh.1 ≠ minted.token.id :=
  FreshSupply.never_reissued reachable minted.issuedAfter

end MintedStackScope

/-- Checked stack object bound to one exact minted lexical scope. -/
structure ScopedStackObject {profile : LayoutProfile}
    {checked : CheckedStackLayout profile} (token : StackScopeToken checked) where
  slot : StackObjectRef checked
  scopeExact : slot.object.scope = token.scopeRef.scope.id

/-- `bindStackObject?` returns a `ScopedStackObject` only after exact scope matching. -/
def bindStackObject? {profile : LayoutProfile}
    {checked : CheckedStackLayout profile} (token : StackScopeToken checked)
    (slot : StackObjectRef checked) : Option (ScopedStackObject token) :=
  if exact : slot.object.scope = token.scopeRef.scope.id then
    some ⟨slot, exact⟩
  else none

end Grass.Construct
