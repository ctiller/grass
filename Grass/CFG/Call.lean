import Grass.CFG.Graph
import Grass.CFG.Stack

/-!
# Abstract call contracts

Calls expose an explicit finite outcome family.  This layer neither assumes a
generic normal return nor invents fault, pending, cancellation, interruption,
violation, or unwind outcomes.  Platform and ABI owners provide the concrete
families and stack shapes consumed here.
-/

namespace Grass.CFG

universe u v

/-- Stable identity of an external call contract. -/
structure ExternalCallId where
  id : StableId
deriving Repr, DecidableEq, Hashable

/-- A call either enters a local callable region or invokes an external
contract supplied by another layer. -/
inductive CallTarget where
  | local (entry : BlockId)
  | external (contract : ExternalCallId)
deriving Repr, DecidableEq

/-- Observable classes of call completion.  Repeating a class is permitted
when a provider contract distinguishes multiple named outcomes in that class. -/
inductive CallOutcomeKind where
  | normal
  | fault
  | pending
  | cancellation
  | interruption
  | violation
  | unwind
deriving Repr, DecidableEq

/-- One explicitly supported call outcome. -/
structure CallOutcomeContract (State : Type u) where
  tag : ExitTag
  kind : CallOutcomeKind
  ensures : State → Prop
  stack : StackShape

/-- Complete abstract contract selected for one call site. -/
structure CallContract (State : Type u) where
  requires : State → Prop
  entryStack : StackShape
  outcomes : List (CallOutcomeContract State)

namespace CallContract

variable {State : Type u}

/-- Outcome identities in contract order. -/
def outcomeTags (contract : CallContract State) : List ExitTag :=
  contract.outcomes.map CallOutcomeContract.tag

/-- Structural validity of an abstract call contract. -/
def wellFormed (contract : CallContract State) : Bool :=
  contract.entryStack.wellFormed &&
  decide contract.outcomeTags.Nodup &&
  contract.outcomes.all fun outcome => outcome.stack.wellFormed

/-- Certificate-facing statement for `CallContract.wellFormed`. -/
def WellFormed (contract : CallContract State) : Prop := contract.wellFormed = true

instance (contract : CallContract State) : Decidable contract.WellFormed :=
  inferInstanceAs (Decidable (contract.wellFormed = true))

/-- Public decomposition of call-contract structural validity. -/
@[simp] theorem wellFormed_iff (contract : CallContract State) :
    contract.WellFormed ↔
      (contract.entryStack.WellFormed ∧ contract.outcomeTags.Nodup) ∧
      (contract.outcomes.all fun outcome => outcome.stack.wellFormed) = true := by
  simp [WellFormed, wellFormed, StackShape.WellFormed]

/-- View a call contract as an ordinary block-boundary contract without losing
or adding any exit. -/
def toBlockContract (contract : CallContract State) : BlockContract State where
  requires := contract.requires
  exits := contract.outcomes.map fun outcome => ⟨outcome.tag, outcome.ensures⟩

@[simp] theorem toBlockContract_exitTags (contract : CallContract State) :
    contract.toBlockContract.exitTags = contract.outcomeTags := by
  simp [toBlockContract, outcomeTags, BlockContract.exitTags]

/-- Forgetting call-specific stack and outcome-class data preserves the exact
block exit-family validity required by the generic CFG layer. -/
theorem toBlockContract_wellFormed (contract : CallContract State)
    (h : contract.WellFormed) : contract.toBlockContract.WellFormed := by
  rw [BlockContract.wellFormed_iff, toBlockContract_exitTags]
  exact (wellFormed_iff contract).mp h |>.1.2

end CallContract

/-- Destination selected for one declared call outcome. -/
structure CallReturn (Terminal : Type v) where
  tag : ExitTag
  target : EdgeTarget Terminal
deriving Repr, DecidableEq

/-- One call occurrence after target and contract selection. -/
structure CallSite (State : Type u) (Terminal : Type v) where
  target : CallTarget
  contract : CallContract State
  actualEntryStack : StackShape
  returns : List (CallReturn Terminal)

namespace CallSite

variable {State : Type u} {Terminal : Type v}

/-- Return identities in authored order. -/
def returnTags (site : CallSite State Terminal) : List ExitTag :=
  site.returns.map CallReturn.tag

/-- Executable local check: the contract is structurally valid, the current
stack has the exact required shape, and every supported outcome is routed once
in canonical contract order. -/
def wellFormed (site : CallSite State Terminal) : Bool :=
  site.contract.wellFormed &&
  site.actualEntryStack.compatible site.contract.entryStack &&
  decide (site.returnTags = site.contract.outcomeTags)

/-- Certificate-facing statement for `CallSite.wellFormed`. -/
def WellFormed (site : CallSite State Terminal) : Prop := site.wellFormed = true

instance (site : CallSite State Terminal) : Decidable site.WellFormed :=
  inferInstanceAs (Decidable (site.wellFormed = true))

/-- Public decomposition of call-site closure. -/
@[simp] theorem wellFormed_iff (site : CallSite State Terminal) :
    site.WellFormed ↔
      (site.contract.WellFormed ∧
        site.actualEntryStack = site.contract.entryStack) ∧
      site.returnTags = site.contract.outcomeTags := by
  simp [WellFormed, wellFormed, CallContract.WellFormed,
    StackShape.compatible_iff]

end CallSite

end Grass.CFG
