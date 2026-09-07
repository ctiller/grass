import Grass.Construct.StackScopeSession

/-!
# Nested generative stack scopes

`StackScopeNest` threads the exact output supply of one checked scope session
into a second session. The inner resource payload may depend on the outer token,
while its enclosing `StackScopeResource` remains indexed by the separately
minted inner token. This is the construction-level composition needed by nested
lexical binders; execution-level provenance elimination remains a later seam.
-/

namespace Grass.Construct

open Grass.Core Grass.CFG Grass.Construct.Layout

universe u v w

/-- Two checked lexical scope sessions minted sequentially in one supply history. -/
structure StackScopeNest {State : Type u} {profile : LayoutProfile}
    (before : StackScopeSupply)
    (outerChecked innerChecked : CheckedStackLayout profile)
    (outerContract innerContract : BlockContract State)
    (OuterResource : Type v) (InnerResource : StackScopeId → Type w) where
  outer : StackScopeSession before outerChecked outerContract OuterResource
  inner : StackScopeSession outer.after innerChecked innerContract
    (InnerResource outer.token.id)
  innerParentExact : inner.token.scopeRef.scope.parent =
    some outer.token.scopeRef.scope.id

namespace StackScopeNest

variable {State : Type u} {profile : LayoutProfile}
  {before : StackScopeSupply}
  {outerChecked innerChecked : CheckedStackLayout profile}
  {outerContract innerContract : BlockContract State}
  {OuterResource : Type v} {InnerResource : StackScopeId → Type w}

/-- The input supply reaches the outer session's exact output supply. -/
theorem beforeToOuter
    (nest : StackScopeNest before outerChecked innerChecked outerContract
      innerContract OuterResource InnerResource) :
    FreshSupply.Reachable before nest.outer.after := by
  rw [nest.outer.afterExact]
  exact .mint (.refl before)

/-- The outer supply reaches the inner session's exact output supply. -/
theorem outerToInner
    (nest : StackScopeNest before outerChecked innerChecked outerContract
      innerContract OuterResource InnerResource) :
    FreshSupply.Reachable nest.outer.after nest.inner.after := by
  rw [nest.inner.afterExact]
  exact .mint (.refl nest.outer.after)

/-- The nested pair advances along one continuous two-mint supply history. -/
theorem beforeToInner
    (nest : StackScopeNest before outerChecked innerChecked outerContract
      innerContract OuterResource InnerResource) :
    FreshSupply.Reachable before nest.inner.after :=
  nest.beforeToOuter.trans nest.outerToInner

/-- The completed inner session still records the outer token as issued. -/
theorem outerIssuedAfterInner
    (nest : StackScopeNest before outerChecked innerChecked outerContract
      innerContract OuterResource InnerResource) :
    nest.inner.after.Issued nest.outer.token.id :=
  nest.outer.issuedAfter.mono nest.outerToInner

/-- `StackScopeNest.innerTokenDistinct` proves the sequential inner mint is fresh. -/
theorem innerTokenDistinct
    (nest : StackScopeNest before outerChecked innerChecked outerContract
      innerContract OuterResource InnerResource) :
    nest.inner.token.id ≠ nest.outer.token.id := by
  rw [nest.inner.tokenExact]
  exact nest.outer.neverReissued (.refl nest.outer.after)

end StackScopeNest

/-- Structured nested-scope rejection retaining the failing lexical stage. -/
inductive StackScopeNestError where
  | outer (error : StackScopeError)
  | inner (error : StackScopeError)
  | parentMismatch (actual : Option ScopeId) (expected : ScopeId)
deriving Repr, DecidableEq

/--
Check an outer session, then check an inner session from its exact output supply.

`checkStackScopeNest` selects the inner payload and ledger from the minted outer
identity, so nested resources may refer to the surrounding lexical scope
without weakening the inner token's distinct nominal index.
-/
def checkStackScopeNest {State : Type u} {profile : LayoutProfile}
    (before : StackScopeSupply)
    (outerChecked innerChecked : CheckedStackLayout profile)
    (outerScopeRef : StackScopeRef outerChecked)
    (innerScopeRef : StackScopeRef innerChecked)
    (outerContract innerContract : BlockContract State)
    (OuterResource : Type v) (InnerResource : StackScopeId → Type w)
    (outerLedgerFor : (id : StackScopeId) →
      StackScopeLedger outerContract (StackScopeResource id OuterResource))
    (innerLedgerFor : (outerId innerId : StackScopeId) →
      StackScopeLedger innerContract
        (StackScopeResource innerId (InnerResource outerId))) :
    Except StackScopeNestError
      (StackScopeNest before outerChecked innerChecked outerContract
        innerContract OuterResource InnerResource) :=
  match checkStackScopeSession before outerChecked outerScopeRef outerContract
      OuterResource outerLedgerFor with
  | .error error => .error (.outer error)
  | .ok outer =>
      match checkStackScopeSession outer.after innerChecked innerScopeRef innerContract
          (InnerResource outer.token.id) (innerLedgerFor outer.token.id) with
      | .error error => .error (.inner error)
      | .ok inner =>
          if nested : inner.token.scopeRef.scope.parent =
              some outer.token.scopeRef.scope.id then
            .ok ⟨outer, inner, nested⟩
          else
            .error (.parentMismatch inner.token.scopeRef.scope.parent
              outer.token.scopeRef.scope.id)

end Grass.Construct
