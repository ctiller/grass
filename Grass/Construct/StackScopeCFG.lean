import Grass.CFG.Stack
import Grass.Construct.StackScopeSession

/-!
# Stack-scope sessions at CFG boundaries

`StackScopeIdModel` injectively maps declared layout scopes into the stable CFG
scope vocabulary. `StackScopeBoundary` then couples a token-indexed, all-exit
closed `StackScopeSession` to exact `StackShape.enterScope?` evidence. Its exit
theorem combines resource closure with LIFO restoration to the original shape.

The nominal `StackScopeToken` remains distinct from the stable CFG identity:
the former distinguishes dynamic construction occurrences, while the latter is
the authored scope name recorded in graph boundary shapes.
-/

namespace Grass.Construct

open Grass.Core Grass.CFG Grass.Construct.Layout

universe u v

/-- Injective encoding of declared layout-scope identities into CFG identities. -/
structure StackScopeIdModel where
  toCFG : ScopeId → Grass.CFG.StackScopeId
  injective : Function.Injective toCFG

/-- One checked session paired with its exact CFG stack-shape entry. -/
structure StackScopeBoundary {State : Type u} {profile : LayoutProfile}
    {beforeSupply : StackScopeSupply} {checked : CheckedStackLayout profile}
    {contract : BlockContract State} {Resource : Type v}
    (model : StackScopeIdModel)
    (session : StackScopeSession beforeSupply checked contract Resource)
    (before : StackShape) where
  entered : StackShape
  beforeValid : before.WellFormed
  enteredExact : before.enterScope? (model.toCFG session.token.scopeRef.scope.id) =
    some entered

namespace StackScopeBoundary

variable {State : Type u} {profile : LayoutProfile}
  {beforeSupply : StackScopeSupply} {checked : CheckedStackLayout profile}
  {contract : BlockContract State} {Resource : Type v}
  {model : StackScopeIdModel}
  {session : StackScopeSession beforeSupply checked contract Resource}
  {before : StackShape}

/-- Stable CFG identity of the boundary's exact declared lexical scope. -/
def scopeId (_boundary : StackScopeBoundary model session before) :
    Grass.CFG.StackScopeId :=
  model.toCFG session.token.scopeRef.scope.id

/-- The exact stable scope identity was not open before this boundary. -/
theorem scopeNotOpenBefore (boundary : StackScopeBoundary model session before) :
    boundary.scopeId ∉ before.openScopes := by
  intro member
  have enteredExact := boundary.enteredExact
  simp [StackShape.enterScope?] at enteredExact
  exact enteredExact.1 member

/-- Scope entry changes only the open-scope stack, placing this scope at its head. -/
theorem enteredShapeExact (boundary : StackScopeBoundary model session before) :
    boundary.entered =
      { before with openScopes := boundary.scopeId :: before.openScopes } := by
  have enteredExact := boundary.enteredExact
  simp only [StackShape.enterScope?] at enteredExact
  split at enteredExact
  · contradiction
  · exact (Option.some.inj enteredExact).symm

/-- `enteredDepthExact` states that lexical scope entry preserves the reserved byte depth. -/
theorem enteredDepthExact (boundary : StackScopeBoundary model session before) :
    boundary.entered.depth = before.depth := by
  rw [boundary.enteredShapeExact]

/-- The entered scope is the exact innermost open CFG scope. -/
theorem enteredScopesExact (boundary : StackScopeBoundary model session before) :
    boundary.entered.openScopes = boundary.scopeId :: before.openScopes := by
  rw [boundary.enteredShapeExact]

/-- The entered boundary shape is structurally valid. -/
theorem enteredValid (boundary : StackScopeBoundary model session before) :
    boundary.entered.WellFormed := by
  rw [StackShape.wellFormed_iff]
  have beforeNodup := (StackShape.wellFormed_iff before).mp boundary.beforeValid
  rw [boundary.enteredScopesExact]
  exact List.nodup_cons.mpr ⟨boundary.scopeNotOpenBefore, beforeNodup⟩

/-- Leaving the exact innermost scope restores the original CFG stack shape. -/
theorem leaveExact (boundary : StackScopeBoundary model session before) :
    boundary.entered.leaveScope? boundary.scopeId = some before :=
  StackShape.leaveScope?_enterScope? before boundary.entered boundary.scopeId
    boundary.enteredExact

/--
Every checked session exit closes resources and restores the exact outer shape.
-/
theorem closesExit (boundary : StackScopeBoundary model session before)
    (exit : StackScopeExit (StackScopeResource session.token.id Resource))
    (member : exit ∈ session.closure.ledger.exits) :
    exit.resources.WellFormed ∧
      boundary.entered.leaveScope? boundary.scopeId = some before :=
  ⟨session.exitClosed exit member, boundary.leaveExact⟩

end StackScopeBoundary

/-- Structured CFG stack-scope boundary rejection. -/
inductive StackScopeBoundaryError where
  | invalidBefore
  | scopeAlreadyOpen (scope : Grass.CFG.StackScopeId)
deriving Repr, DecidableEq

/-- Validate the outer shape and enter the session's exact stable scope identity. -/
def checkStackScopeBoundary {State : Type u} {profile : LayoutProfile}
    {beforeSupply : StackScopeSupply} {checked : CheckedStackLayout profile}
    {contract : BlockContract State} {Resource : Type v}
    (model : StackScopeIdModel)
    (session : StackScopeSession beforeSupply checked contract Resource)
    (before : StackShape) :
    Except StackScopeBoundaryError (StackScopeBoundary model session before) :=
  if valid : before.WellFormed then
    match enteredExact : before.enterScope?
        (model.toCFG session.token.scopeRef.scope.id) with
    | none =>
        .error (.scopeAlreadyOpen (model.toCFG session.token.scopeRef.scope.id))
    | some entered => .ok ⟨entered, valid, enteredExact⟩
  else
    .error .invalidBefore

end Grass.Construct
