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

universe u v u₁ u₂

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

/-- Find the first explicitly supported outcome with the requested exit tag. -/
def findOutcome? (contract : CallContract State) (tag : ExitTag) :
    Option (CallOutcomeContract State) :=
  contract.outcomes.find? fun outcome => outcome.tag == tag

/-- A successful outcome lookup returns an authored contract member carrying
the requested exit tag. -/
theorem findOutcome?_sound
    (contract : CallContract State) (tag : ExitTag)
    (outcome : CallOutcomeContract State)
    (found : contract.findOutcome? tag = some outcome) :
    outcome ∈ contract.outcomes ∧ outcome.tag = tag := by
  constructor
  · exact List.mem_of_find?_eq_some (by
      simpa [findOutcome?] using found)
  · have matched : outcome.tag == tag := List.find?_some
      (p := fun candidate : CallOutcomeContract State => candidate.tag == tag) (by
        simpa [findOutcome?] using found)
    exact LawfulBEq.eq_of_beq matched

/-- Outcome lookup succeeds exactly for an explicitly supported outcome tag. -/
theorem findOutcome?_isSome_iff_mem_outcomeTags
    (contract : CallContract State) (tag : ExitTag) :
    (contract.findOutcome? tag).isSome = true ↔ tag ∈ contract.outcomeTags := by
  simp [findOutcome?, outcomeTags]

/-- Every explicitly supported outcome tag has a concrete outcome contract. -/
theorem outcomeForTag
    (contract : CallContract State) (tag : ExitTag)
    (member : tag ∈ contract.outcomeTags) :
    ∃ outcome, contract.findOutcome? tag = some outcome := by
  apply Option.isSome_iff_exists.mp
  exact (contract.findOutcome?_isSome_iff_mem_outcomeTags tag).2 member

/-- Structural validity of an abstract call contract. -/
def wellFormed (contract : CallContract State) : Bool :=
  contract.entryStack.wellFormed &&
  decide contract.outcomeTags.Nodup &&
  contract.outcomes.all fun outcome => outcome.stack.wellFormed

/-- Certificate-facing statement for `CallContract.wellFormed`. -/
def WellFormed (contract : CallContract State) : Prop := contract.wellFormed = true

instance (contract : CallContract State) : Decidable contract.WellFormed :=
  inferInstanceAs (Decidable (contract.wellFormed = true))

/-- Every declared outcome carries a structurally valid exit stack shape. -/
def OutcomesWellFormed (contract : CallContract State) : Prop :=
  ∀ outcome ∈ contract.outcomes, outcome.stack.WellFormed

theorem outcomesWellFormed_iff_all (contract : CallContract State) :
    contract.OutcomesWellFormed ↔
      (contract.outcomes.all fun outcome => outcome.stack.wellFormed) = true := by
  simp [OutcomesWellFormed, StackShape.WellFormed]

/-- Public decomposition of call-contract structural validity. -/
@[simp] theorem wellFormed_iff (contract : CallContract State) :
    contract.WellFormed ↔
      (contract.entryStack.WellFormed ∧ contract.outcomeTags.Nodup) ∧
      contract.OutcomesWellFormed := by
  simp [WellFormed, wellFormed, StackShape.WellFormed,
    outcomesWellFormed_iff_all]

theorem entryStackWellFormed_of_wellFormed (contract : CallContract State)
    (h : contract.WellFormed) : contract.entryStack.WellFormed :=
  (wellFormed_iff contract).mp h |>.1.1

theorem outcomeTagsNodup_of_wellFormed (contract : CallContract State)
    (h : contract.WellFormed) : contract.outcomeTags.Nodup :=
  (wellFormed_iff contract).mp h |>.1.2

theorem outcomesWellFormed_of_wellFormed (contract : CallContract State)
    (h : contract.WellFormed) : contract.OutcomesWellFormed :=
  (wellFormed_iff contract).mp h |>.2

private theorem eq_of_mem_of_mem_of_map_nodup
    {α : Type u₁} {β : Type u₂} (key : α → β)
    {items : List α} {left right : α}
    (unique : (items.map key).Nodup)
    (leftMem : left ∈ items) (rightMem : right ∈ items)
    (sameKey : key left = key right) : left = right := by
  induction items with
  | nil => simp at leftMem
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at unique
      rw [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          apply unique.1
          rw [sameKey]
          exact List.mem_map.mpr ⟨right, rightMem, rfl⟩
      · rcases rightMem with rfl | rightMem
        · exfalso
          apply unique.1
          rw [← sameKey]
          exact List.mem_map.mpr ⟨left, leftMem, rfl⟩
        · exact ih unique.2 leftMem rightMem

/-- `CallContract.outcome_eq_of_mem_of_mem_of_tag_eq` proves that two outcomes
of a valid contract with the same tag are the same function-bearing outcome. -/
theorem outcome_eq_of_mem_of_mem_of_tag_eq
    (contract : CallContract State) (left right : CallOutcomeContract State)
    (closed : contract.WellFormed)
    (leftMem : left ∈ contract.outcomes) (rightMem : right ∈ contract.outcomes)
    (sameTag : left.tag = right.tag) : left = right := by
  exact eq_of_mem_of_mem_of_map_nodup CallOutcomeContract.tag
    (contract.outcomeTagsNodup_of_wellFormed closed) leftMem rightMem sameTag

/-- Under `CallContract.WellFormed`, outcome lookup returns the exact authored
member already held by the caller. -/
theorem findOutcome?_eq_some_of_mem
    (contract : CallContract State) (tag : ExitTag)
    (outcome : CallOutcomeContract State) (closed : contract.WellFormed)
    (member : outcome ∈ contract.outcomes) (hasTag : outcome.tag = tag) :
    contract.findOutcome? tag = some outcome := by
  have tagMember : tag ∈ contract.outcomeTags := by
    simp [outcomeTags]
    exact ⟨outcome, member, hasTag⟩
  obtain ⟨found, foundLookup⟩ := contract.outcomeForTag tag tagMember
  have foundFacts := contract.findOutcome?_sound tag found foundLookup
  have foundEq : found = outcome :=
    contract.outcome_eq_of_mem_of_mem_of_tag_eq found outcome closed
      foundFacts.1 member (foundFacts.2.trans hasTag.symm)
  simpa [foundEq] using foundLookup

/-- View a call contract as an ordinary block-boundary contract without losing
or adding any exit. -/
def toBlockContract (contract : CallContract State) : BlockContract State where
  requires := contract.requires
  exits := contract.outcomes.map fun outcome => ⟨outcome.tag, outcome.ensures⟩

@[simp] theorem toBlockContract_exitTags (contract : CallContract State) :
    contract.toBlockContract.exitTags = contract.outcomeTags := by
  simp [toBlockContract, outcomeTags, BlockContract.exitTags]

/-- `CallContract.toBlockContract_wellFormed` preserves generic block
exit-family validity while forgetting call-specific stack and outcome data. -/
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

/-- Find the first authored return route with the requested outcome tag. -/
def findReturn? (site : CallSite State Terminal) (tag : ExitTag) :
    Option (CallReturn Terminal) :=
  site.returns.find? fun route => route.tag == tag

/-- A successful return lookup exposes an authored route with the requested
outcome tag. -/
theorem findReturn?_sound
    (site : CallSite State Terminal) (tag : ExitTag) (route : CallReturn Terminal)
    (found : site.findReturn? tag = some route) :
    route ∈ site.returns ∧ route.tag = tag := by
  constructor
  · exact List.mem_of_find?_eq_some (by
      simpa [findReturn?] using found)
  · have matched : route.tag == tag := List.find?_some
      (p := fun candidate : CallReturn Terminal => candidate.tag == tag) (by
        simpa [findReturn?] using found)
    exact LawfulBEq.eq_of_beq matched

/-- Return lookup succeeds exactly for a routed outcome tag. -/
theorem findReturn?_isSome_iff_mem_returnTags
    (site : CallSite State Terminal) (tag : ExitTag) :
    (site.findReturn? tag).isSome = true ↔ tag ∈ site.returnTags := by
  simp [findReturn?, returnTags]

/-- Every routed outcome tag has a concrete return route. -/
theorem returnForTag
    (site : CallSite State Terminal) (tag : ExitTag)
    (member : tag ∈ site.returnTags) :
    ∃ route, site.findReturn? tag = some route := by
  apply Option.isSome_iff_exists.mp
  exact (site.findReturn?_isSome_iff_mem_returnTags tag).2 member

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

theorem contractWellFormed_of_wellFormed (site : CallSite State Terminal)
    (h : site.WellFormed) : site.contract.WellFormed :=
  (wellFormed_iff site).mp h |>.1.1

theorem entryStackExact_of_wellFormed (site : CallSite State Terminal)
    (h : site.WellFormed) :
    site.actualEntryStack = site.contract.entryStack :=
  (wellFormed_iff site).mp h |>.1.2

theorem returnTagsExact_of_wellFormed (site : CallSite State Terminal)
    (h : site.WellFormed) :
    site.returnTags = site.contract.outcomeTags :=
  (wellFormed_iff site).mp h |>.2

/-- A valid call site routes each supported outcome tag at most once. -/
theorem returnTagsNodup_of_wellFormed (site : CallSite State Terminal)
    (closed : site.WellFormed) : site.returnTags.Nodup := by
  rw [site.returnTagsExact_of_wellFormed closed]
  exact site.contract.outcomeTagsNodup_of_wellFormed
    (site.contractWellFormed_of_wellFormed closed)

/-- `CallSite.return_eq_of_mem_of_mem_of_tag_eq` proves that two routes of a
valid call site with the same tag are the same destination. -/
theorem return_eq_of_mem_of_mem_of_tag_eq
    (site : CallSite State Terminal) (left right : CallReturn Terminal)
    (closed : site.WellFormed)
    (leftMem : left ∈ site.returns) (rightMem : right ∈ site.returns)
    (sameTag : left.tag = right.tag) : left = right := by
  exact CallContract.eq_of_mem_of_mem_of_map_nodup CallReturn.tag
    (site.returnTagsNodup_of_wellFormed closed) leftMem rightMem sameTag

/-- Under `CallSite.WellFormed`, return lookup yields the exact route already
held by the caller. -/
theorem findReturn?_eq_some_of_mem
    (site : CallSite State Terminal) (tag : ExitTag) (route : CallReturn Terminal)
    (closed : site.WellFormed) (member : route ∈ site.returns)
    (hasTag : route.tag = tag) : site.findReturn? tag = some route := by
  have tagMember : tag ∈ site.returnTags := by
    simp [returnTags]
    exact ⟨route, member, hasTag⟩
  obtain ⟨found, foundLookup⟩ := site.returnForTag tag tagMember
  have foundFacts := site.findReturn?_sound tag found foundLookup
  have foundEq : found = route :=
    site.return_eq_of_mem_of_mem_of_tag_eq found route closed
      foundFacts.1 member (foundFacts.2.trans hasTag.symm)
  simpa [foundEq] using foundLookup

end CallSite

end Grass.CFG
