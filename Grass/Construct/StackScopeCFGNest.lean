import Grass.Construct.StackScopeCFG
import Grass.Construct.StackScopeNest

/-!
# Nested stack-scope sessions at CFG boundaries

`StackScopeNestBoundary` checks the outer and inner sessions in lexical order.
Its exact-shape theorems expose both stable scope identities at the head of the
CFG stack and prove that leaving them in LIFO order restores the original shape.
-/

namespace Grass.Construct

open Grass.Core Grass.CFG Grass.Construct.Layout

universe u v w

/-- Two nested checked sessions paired with their sequential CFG scope entries. -/
structure StackScopeNestBoundary {State : Type u} {profile : LayoutProfile}
    {beforeSupply : StackScopeSupply}
    {outerChecked innerChecked : CheckedStackLayout profile}
    {outerContract innerContract : BlockContract State}
    {OuterResource : Type v} {InnerResource : StackScopeId → Type w}
    (model : StackScopeIdModel)
    (nest : StackScopeNest beforeSupply outerChecked innerChecked outerContract
      innerContract OuterResource InnerResource)
    (before : StackShape) where
  outer : StackScopeBoundary model nest.outer before
  inner : StackScopeBoundary model nest.inner outer.entered

namespace StackScopeNestBoundary

variable {State : Type u} {profile : LayoutProfile}
  {beforeSupply : StackScopeSupply}
  {outerChecked innerChecked : CheckedStackLayout profile}
  {outerContract innerContract : BlockContract State}
  {OuterResource : Type v} {InnerResource : StackScopeId → Type w}
  {model : StackScopeIdModel}
  {nest : StackScopeNest beforeSupply outerChecked innerChecked outerContract
    innerContract OuterResource InnerResource}
  {before : StackShape}

/-- The nested CFG identities are distinct because the inner entry is fresh. -/
theorem scopeIdsDistinct (boundary : StackScopeNestBoundary model nest before) :
    boundary.inner.scopeId ≠ boundary.outer.scopeId := by
  intro equal
  apply boundary.inner.scopeNotOpenBefore
  rw [boundary.outer.enteredScopesExact]
  simp [equal]

/-- Both stable identities are the exact innermost scopes after nested entry. -/
theorem enteredScopesExact (boundary : StackScopeNestBoundary model nest before) :
    boundary.inner.entered.openScopes =
      boundary.inner.scopeId :: boundary.outer.scopeId :: before.openScopes := by
  rw [boundary.inner.enteredScopesExact, boundary.outer.enteredScopesExact]

/-- `enteredDepthExact` states that nested entry preserves the reserved byte depth. -/
theorem enteredDepthExact (boundary : StackScopeNestBoundary model nest before) :
    boundary.inner.entered.depth = before.depth := by
  rw [boundary.inner.enteredDepthExact, boundary.outer.enteredDepthExact]

/-- The fully entered nested shape is structurally valid. -/
theorem enteredValid (boundary : StackScopeNestBoundary model nest before) :
    boundary.inner.entered.WellFormed :=
  boundary.inner.enteredValid

/-- Leaving inner and then outer restores each exact preceding CFG shape. -/
theorem leaveBothExact (boundary : StackScopeNestBoundary model nest before) :
    boundary.inner.entered.leaveScope? boundary.inner.scopeId =
        some boundary.outer.entered ∧
      boundary.outer.entered.leaveScope? boundary.outer.scopeId = some before :=
  ⟨boundary.inner.leaveExact, boundary.outer.leaveExact⟩

/--
Every selected inner and outer exit closes its resources while exact LIFO
restoration returns to the original outer shape.
-/
theorem closesExits (boundary : StackScopeNestBoundary model nest before)
    (outerExit : StackScopeExit
      (StackScopeResource nest.outer.token.id OuterResource))
    (outerMember : outerExit ∈ nest.outer.closure.ledger.exits)
    (innerExit : StackScopeExit
      (StackScopeResource nest.inner.token.id
        (InnerResource nest.outer.token.id)))
    (innerMember : innerExit ∈ nest.inner.closure.ledger.exits) :
    outerExit.resources.WellFormed ∧ innerExit.resources.WellFormed ∧
      boundary.inner.entered.leaveScope? boundary.inner.scopeId =
        some boundary.outer.entered ∧
      boundary.outer.entered.leaveScope? boundary.outer.scopeId = some before :=
  ⟨nest.outer.exitClosed outerExit outerMember,
    nest.inner.exitClosed innerExit innerMember,
    boundary.inner.leaveExact, boundary.outer.leaveExact⟩

end StackScopeNestBoundary

/-- Structured nested CFG boundary rejection retaining the failing stage. -/
inductive StackScopeNestBoundaryError where
  | outer (error : StackScopeBoundaryError)
  | inner (error : StackScopeBoundaryError)
deriving Repr, DecidableEq

/-- Check exact outer and inner CFG scope entry in lexical order. -/
def checkStackScopeNestBoundary {State : Type u} {profile : LayoutProfile}
    {beforeSupply : StackScopeSupply}
    {outerChecked innerChecked : CheckedStackLayout profile}
    {outerContract innerContract : BlockContract State}
    {OuterResource : Type v} {InnerResource : StackScopeId → Type w}
    (model : StackScopeIdModel)
    (nest : StackScopeNest beforeSupply outerChecked innerChecked outerContract
      innerContract OuterResource InnerResource)
    (before : StackShape) :
    Except StackScopeNestBoundaryError
      (StackScopeNestBoundary model nest before) :=
  match checkStackScopeBoundary model nest.outer before with
  | .error error => .error (.outer error)
  | .ok outer =>
      match checkStackScopeBoundary model nest.inner outer.entered with
      | .error error => .error (.inner error)
      | .ok inner => .ok ⟨outer, inner⟩

end Grass.Construct
