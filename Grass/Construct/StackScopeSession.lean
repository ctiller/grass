import Grass.Construct.StackScope
import Grass.Construct.StackScopeToken

/-!
# Generative stack-scope sessions

`StackScopeSession` couples one exact fresh-token mint with an all-exit closure
certificate whose resource type is indexed by that minted identity. The checked
constructor advances the supplied identity history once and checks the ledger
chosen for the resulting identity.

This is the checked input to a future `withStack` eliminator. It deliberately
still exposes its token: hiding that identity while returning a verified outer
fragment requires the execution model's provenance interpretation and an
elimination law, neither of which construction may fabricate.
-/

namespace Grass.Construct

open Grass.Core Grass.CFG Grass.Construct.Layout

universe u v

/-- Payload owned by one exact nominal stack-scope identity. -/
structure StackScopeResource (owner : StackScopeId) (Resource : Type v) where
  value : Resource

/--
One freshly minted lexical scope paired with closure evidence at every exit.

`StackScopeResource` keeps the minted identity in the closure ledger's resource
type even when two sessions use the same payload type.
-/
structure StackScopeSession {State : Type u} {profile : LayoutProfile}
    (before : StackScopeSupply) (checked : CheckedStackLayout profile)
    (contract : BlockContract State) (Resource : Type v) where
  minted : MintedStackScope before checked
  closure : CheckedStackScope (contract := contract)
    (Resource := StackScopeResource minted.token.id Resource)

namespace StackScopeSession

variable {State : Type u} {profile : LayoutProfile}
  {before : StackScopeSupply} {checked : CheckedStackLayout profile}
  {contract : BlockContract State} {Resource : Type v}

/-- The exact nominal token whose resource family the session closes. -/
def token (session : StackScopeSession before checked contract Resource) :
    StackScopeToken checked :=
  session.minted.token

/-- The supply after the session's single token mint. -/
def after (session : StackScopeSession before checked contract Resource) :
    StackScopeSupply :=
  session.minted.after

/-- The session token was not issued by its input supply. -/
theorem freshBefore (session : StackScopeSession before checked contract Resource) :
    ¬before.Issued session.token.id :=
  session.minted.freshBefore

/-- The session's output supply records its exact token. -/
theorem issuedAfter (session : StackScopeSession before checked contract Resource) :
    session.after.Issued session.token.id :=
  session.minted.issuedAfter

/-- The session token is exactly the identity returned by its one mint. -/
theorem tokenExact (session : StackScopeSession before checked contract Resource) :
    session.token.id = before.fresh.1 :=
  session.minted.idExact

/-- The session output is exactly the supply returned by its one mint. -/
theorem afterExact (session : StackScopeSession before checked contract Resource) :
    session.after = before.fresh.2 :=
  session.minted.afterExact

/-- `StackScopeSession.neverReissued` rules out the token at every reachable later mint. -/
theorem neverReissued (session : StackScopeSession before checked contract Resource)
    {later : StackScopeSupply} (reachable : FreshSupply.Reachable session.after later) :
    later.fresh.1 ≠ session.token.id :=
  session.minted.neverReissued reachable

/-- The session closure covers exactly the contract's ordered exit identities. -/
theorem exitTagsExact (session : StackScopeSession before checked contract Resource) :
    session.closure.ledger.exitTags = contract.exitTags :=
  session.closure.exitTagsExact

/-- Every exit in the token-indexed session ledger is fully closed. -/
theorem exitClosed (session : StackScopeSession before checked contract Resource)
    (exit : StackScopeExit (StackScopeResource session.token.id Resource))
    (member : exit ∈ session.closure.ledger.exits) : exit.resources.WellFormed :=
  session.closure.exitClosed exit member

/-- `StackScopeSession.bindStackObject?` binds only an object in this session's exact scope. -/
def bindStackObject? (session : StackScopeSession before checked contract Resource)
    (slot : StackObjectRef checked) : Option (ScopedStackObject session.token) :=
  Grass.Construct.bindStackObject? session.token slot

end StackScopeSession

/--
Mint exactly one scope identity and check the ledger selected for that identity.

`checkStackScopeSession` accepts a dependent ledger selector so every resource
is wrapped by `StackScopeResource` at the identity being minted. A failure
returns no session, while the caller retains the unchanged input supply value
and may decide whether to retry.
-/
def checkStackScopeSession {State : Type u} {profile : LayoutProfile}
    (before : StackScopeSupply) (checked : CheckedStackLayout profile)
    (scopeRef : StackScopeRef checked) (contract : BlockContract State)
    (Resource : Type v)
    (ledgerFor : (id : StackScopeId) →
      StackScopeLedger contract (StackScopeResource id Resource)) :
    Except StackScopeError (StackScopeSession before checked contract Resource) :=
  let minted := before.mint checked scopeRef
  match checkStackScope (ledgerFor minted.token.id) with
  | .error error => .error error
  | .ok closure => .ok ⟨minted, closure⟩

end Grass.Construct
