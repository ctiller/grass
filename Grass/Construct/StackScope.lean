import Grass.CFG.Contract
import Grass.Construct.Layout.Stack

/-!
# Exact lexical stack-scope exit closure

`StackScopeLedger` assigns one resource ledger to every block-contract exit in
the same order and by exact exit identity. `CheckedStackScope` proves the
contract is structurally valid and every listed exit has no escaping address,
live loan, or live obligation. This is the all-exit closure input required by a
future provenance-indexed `withStack` eliminator.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Layout

universe u v

/-- Resource state observed at one exact contract exit. -/
structure StackScopeExit (Resource : Type v) where
  tag : ExitTag
  resources : ScopeExit Resource

/-- Ordered resource ledgers for every exit of one exact block contract. -/
structure StackScopeLedger {State : Type u}
    (contract : BlockContract State) (Resource : Type v) where
  exits : List (StackScopeExit Resource)

namespace StackScopeLedger

variable {State : Type u} {Resource : Type v} {contract : BlockContract State}

/-- Exit identities recorded by the scope ledger. -/
def exitTags (scope : StackScopeLedger contract Resource) : List ExitTag :=
  scope.exits.map StackScopeExit.tag

/-- Executable exact all-exit scope-closure check. -/
def wellFormed (scope : StackScopeLedger contract Resource) : Bool :=
  contract.wellFormed &&
    decide (scope.exitTags = contract.exitTags) &&
    scope.exits.all fun exit => exit.resources.wellFormed

/-- Certificate-facing statement for `StackScopeLedger.wellFormed`. -/
def WellFormed (scope : StackScopeLedger contract Resource) : Prop :=
  scope.wellFormed = true

instance (scope : StackScopeLedger contract Resource) : Decidable scope.WellFormed :=
  inferInstanceAs (Decidable (scope.wellFormed = true))

@[simp] theorem wellFormed_iff (scope : StackScopeLedger contract Resource) :
    scope.WellFormed ↔
      (contract.WellFormed ∧ scope.exitTags = contract.exitTags) ∧
        scope.exits.all (fun exit => exit.resources.wellFormed) = true := by
  simp [WellFormed, wellFormed, BlockContract.WellFormed]

end StackScopeLedger

/-- One exact stack-scope ledger paired with its all-exit closure certificate. -/
structure CheckedStackScope {State : Type u} {Resource : Type v}
    {contract : BlockContract State} where
  ledger : StackScopeLedger contract Resource
  valid : ledger.WellFormed

namespace CheckedStackScope

variable {State : Type u} {Resource : Type v} {contract : BlockContract State}

/-- A checked scope's exit identities equal its contract's identities exactly. -/
theorem exitTagsExact (scope : CheckedStackScope (contract := contract)
    (Resource := Resource)) : scope.ledger.exitTags = contract.exitTags :=
  (StackScopeLedger.wellFormed_iff scope.ledger).mp scope.valid |>.1.2

/-- Every resource ledger in a checked scope is closed. -/
theorem exitClosed (scope : CheckedStackScope (contract := contract)
    (Resource := Resource)) (exit : StackScopeExit Resource)
    (member : exit ∈ scope.ledger.exits) : exit.resources.WellFormed := by
  have closed := (StackScopeLedger.wellFormed_iff scope.ledger).mp scope.valid |>.2
  exact List.all_eq_true.mp closed exit member

end CheckedStackScope

/-- Structured rejection from exact stack-scope closure checking. -/
inductive StackScopeError where
  | invalidContract
  | exitTagsMismatch (actual expected : List ExitTag)
  | openExit (tag : ExitTag)
deriving Repr, DecidableEq

/-- Check structural validity, exact exit coverage, and closure of every exit. -/
def checkStackScope {State : Type u} {Resource : Type v}
    {contract : BlockContract State} (scope : StackScopeLedger contract Resource) :
    Except StackScopeError (CheckedStackScope (contract := contract)
      (Resource := Resource)) :=
  if _contract : contract.WellFormed then
    if _tags : scope.exitTags = contract.exitTags then
      match found : scope.exits.find? fun exit => !exit.resources.wellFormed with
      | some exit => .error (.openExit exit.tag)
      | none =>
          have noOpen : ∀ exit ∈ scope.exits,
              ¬(!exit.resources.wellFormed) = true :=
            List.find?_eq_none.mp found
          have closed : scope.exits.all
              (fun exit => exit.resources.wellFormed) = true := by
            apply List.all_eq_true.mpr
            intro exit member
            simpa using noOpen exit member
          have valid : scope.WellFormed :=
            (StackScopeLedger.wellFormed_iff scope).mpr
              ⟨⟨_contract, _tags⟩, closed⟩
          .ok ⟨scope, valid⟩
    else .error (.exitTagsMismatch scope.exitTags contract.exitTags)
  else .error .invalidContract

end Grass.Construct
