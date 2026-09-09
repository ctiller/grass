import Grass.Op.Step
import Grass.Memory.LoanBatch
import Grass.Memory.GrantMint

/-!
# Occurrence-bound synchronous loan bookkeeping

This layer couples a batch of loans to a request and a fresh call occurrence.
`handoff?` and `return?` publish the machine, supplies, pending table, and boundary
trace together. An `Option.none` exposes no partially updated state.

This is not an ABI-return certificate or a happens-before model. Boundary events
record this protocol's transitions; an instruction/provider refinement must
still connect them to actual calls and returns. In particular, the conservative
cross-context conflict checks in `Grass.Op.step` are unchanged.
-/

namespace Grass.Op.CallProtocol

open Grass.Core Grass.Memory Grass.Std.Logical

inductive CallTag
abbrev CallId := Uid CallTag

/-- A requested loan without an identity or a choice of lender/holder. -/
structure LoanRequest where
  kind : GrantKind
  provenance : Provenance
  range : ByteRange
  rights : Permission

def LoanRequest.grant (request : LoanRequest) (caller agent : ContextId) : AuthorityGrant :=
  { kind := request.kind, provenance := request.provenance, range := request.range,
    rights := request.rights, lender := caller, holder := agent }

structure Pending (Request : Type) where
  caller : ContextId
  agent : ContextId
  request : Request
  loans : LoanBatch.Entries

def Pending.ids {Request : Type} (pending : Pending Request) : List GrantId :=
  pending.loans.map Prod.fst

/-- Protocol boundaries, distinct from memory-access events. -/
inductive Boundary where
  | handoff (call : CallId) (caller agent : ContextId) (loans : List GrantId)
  | returned (call : CallId) (caller agent : ContextId) (loans : List GrantId)

/-- `GrantSupplyCovers` checks the supplied grant-domain history against currently
recorded grants. Covering previously retired identities is an integration
obligation; those identities are not represented in the current live map. -/
def GrantSupplyCovers (memory : MemoryState) (supply : FreshSupply GrantTag) : Prop :=
  ∀ entry ∈ memory.grantEntries, supply.Issued entry.1

instance (memory : MemoryState) (supply : FreshSupply GrantTag) :
    Decidable (GrantSupplyCovers memory supply) :=
  inferInstanceAs (Decidable (∀ entry ∈ memory.grantEntries, supply.Issued entry.1))

def Pending.Valid {Request : Type} (pending : Pending Request) (memory : MemoryState) : Prop :=
  LoanBatch.DistinctIds pending.loans ∧
    (∀ entry ∈ pending.loans,
      entry.2.lender = pending.caller ∧ entry.2.holder = pending.agent) ∧
    LoanBatch.Matches memory pending.loans

instance {Request : Type} (pending : Pending Request) (memory : MemoryState) :
    Decidable (pending.Valid memory) := by
  unfold Pending.Valid LoanBatch.DistinctIds LoanBatch.Matches
  infer_instance

def PendingTableValid {Request : Type} (memory : MemoryState)
    (supply : FreshSupply CallTag) (pending : FiniteMap CallId (Pending Request)) : Prop :=
  pending.entries.Pairwise (fun left right => left.2.caller ≠ right.2.caller) ∧
    ∀ entry ∈ pending.entries, supply.Issued entry.1 ∧ entry.2.Valid memory

instance {Request : Type} (memory : MemoryState) (supply : FreshSupply CallTag)
    (pending : FiniteMap CallId (Pending Request)) :
    Decidable (PendingTableValid memory supply pending) :=
  inferInstanceAs (Decidable
    (pending.entries.Pairwise (fun left right => left.2.caller ≠ right.2.caller) ∧
      ∀ entry ∈ pending.entries, supply.Issued entry.1 ∧ entry.2.Valid memory))

/-- State for the checked protocol doors. Invariants concern loan bookkeeping,
not the validity of arbitrary initial machine executions. -/
structure State (Request : Type) where
  private mk ::
  machine : MachineState
  callSupply : FreshSupply CallTag
  grantSupply : FreshSupply GrantTag
  pending : FiniteMap CallId (Pending Request)
  boundaries : List Boundary
  grantsCovered : GrantSupplyCovers machine.memory grantSupply
  pendingValid : PendingTableValid machine.memory callSupply pending

def initial {Request : Type} (machine : MachineState) (supply : FreshSupply GrantTag)
    (covered : GrantSupplyCovers machine.memory supply) : State Request :=
  ⟨machine, .initial, supply, .empty, [], covered, by
    simp [PendingTableValid, FiniteMap.empty]⟩

private def checked? {Request : Type} (machine : MachineState)
    (callSupply : FreshSupply CallTag) (grantSupply : FreshSupply GrantTag)
    (pending : FiniteMap CallId (Pending Request)) (boundaries : List Boundary) :
    Option (State Request) :=
  if covered : GrantSupplyCovers machine.memory grantSupply then
    if valid : PendingTableValid machine.memory callSupply pending then
      some ⟨machine, callSupply, grantSupply, pending, boundaries, covered, valid⟩
    else none
  else none

/-- A synchronous caller remains suspended until its pending boundary returns. -/
def callerPending {Request : Type} (state : State Request) (caller : ContextId) : Bool :=
  state.pending.entries.any (fun entry => decide (entry.2.caller = caller))

def handoff? {Request : Type} (state : State Request) (caller agent : ContextId)
    (request : Request) (loans : List LoanRequest) : Option (CallId × State Request) := do
  if caller = agent ∨ callerPending state caller = true ∨
      (state.machine.contexts.lookup caller).isNone = true then none else do
  let call := state.callSupply.fresh
  let minted := GrantMint.mint state.grantSupply (loans.map (fun loan => loan.grant caller agent))
  let memory ← LoanBatch.issue? state.machine.memory caller minted.1
  let record : Pending Request := ⟨caller, agent, request, minted.1⟩
  if (state.pending.lookup call.1).isSome then none else do
    let next ← checked? { state.machine with memory := memory } call.2 minted.2
      (state.pending.insert call.1 record)
      (state.boundaries ++ [.handoff call.1 caller agent record.ids])
    pure (call.1, next)

/-- Complete the loan bookkeeping for the exact pending occurrence. The stored
request is returned for subsequent dependent provider-result checking; this
function supplies no evidence that the physical ABI return occurred. -/
def return? {Request : Type} (state : State Request) (call : CallId)
    (caller agent : ContextId) (ids : List GrantId) :
    Option (Pending Request × State Request) := do
  let record ← state.pending.lookup call
  if record.caller ≠ caller ∨ record.agent ≠ agent ∨ record.ids ≠ ids then none else do
    let memory ← LoanBatch.return? state.machine.memory caller record.loans
    let next ← checked? { state.machine with memory := memory }
      state.callSupply state.grantSupply (state.pending.erase call)
      (state.boundaries ++ [.returned call caller agent ids])
    pure (record, next)

/-- Ordinary steps in this initial protocol slice declare no authority-map
effects. Even a return-and-reissue sequence with identical final bindings is
therefore excluded; reserved loans change only through the boundary doors. -/
def authorityFree (operation : SomeOperation) : Bool :=
  match operation.facets.substeps? with
  | none => false
  | some sequence => sequence.accesses.all (fun access => access.authorityEffect.isEmpty)

/-- Run the existing operation semantics, retaining all bookkeeping invariants.
This bounded wrapper supports ordinary accesses, not unrelated loan operations. -/
def step? {Request : Type} (state : State Request) (policy : StepPolicy)
    (operation : SomeOperation) (context : ContextId) (kind : ContextKind)
    (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none) :
    Option (State Request) :=
  if callerPending state context then none else if authorityFree operation then
    match Grass.Op.step policy state.machine operation context kind cause faultAt with
    | .rejected _ => none
    | .ran machine => checked? machine state.callSupply state.grantSupply
        state.pending state.boundaries
  else none

private theorem checked?_fields {Request : Type} {machine : MachineState}
    {callSupply : FreshSupply CallTag} {grantSupply : FreshSupply GrantTag}
    {pending : FiniteMap CallId (Pending Request)} {boundaries : List Boundary}
    {next : State Request}
    (success : checked? machine callSupply grantSupply pending boundaries = some next) :
    next.machine = machine ∧ next.callSupply = callSupply ∧
      next.grantSupply = grantSupply ∧ next.pending = pending ∧
      next.boundaries = boundaries := by
  unfold checked? at success
  split at success
  · split at success
    · cases success
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp at success
  · simp at success

/-- A successful return identifies the exact pending occurrence it consumed. -/
theorem return?_matches_occurrence {Request : Type} {state next : State Request}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    {record : Pending Request}
    (success : return? state call caller agent ids = some (record, next)) :
    state.pending.lookup call = some record ∧ record.caller = caller ∧
      record.agent = agent ∧ record.ids = ids := by
  unfold return? at success
  cases lookup : state.pending.lookup call with
  | none => simp [lookup] at success
  | some found =>
      simp only [lookup, Option.bind_eq_bind, Option.bind_some] at success
      split at success
      · simp at success
      · next exactMatch =>
          simp only [not_or] at exactMatch
          cases returned : LoanBatch.return? state.machine.memory caller found.loans with
          | none => simp [returned] at success
          | some memory =>
              simp only [returned, Option.bind_some] at success
              cases checked : checked? { state.machine with memory := memory }
                  state.callSupply state.grantSupply (state.pending.erase call)
                  (state.boundaries ++ [.returned call caller agent ids]) with
              | none => simp [checked] at success
              | some checkedState =>
                  simp only [checked, Option.bind_some] at success
                  rcases success with ⟨rfl, rfl⟩
                  refine ⟨rfl, ?_, ?_, ?_⟩
                  · exact Classical.byContradiction exactMatch.1
                  · exact Classical.byContradiction exactMatch.2.1
                  · exact Classical.byContradiction exactMatch.2.2

/-- Named observations of a successful bookkeeping return. -/
structure ReturnEffects {Request : Type} (before after : State Request)
    (call : CallId) (caller agent : ContextId) (ids : List GrantId)
    (record : Pending Request) : Prop where
  occurrence : before.pending.lookup call = some record
  callerMatches : record.caller = caller
  agentMatches : record.agent = agent
  idsMatch : record.ids = ids
  loansReturned : LoanBatch.return? before.machine.memory caller record.loans =
    some after.machine.memory
  machineUpdated : after.machine = { before.machine with memory := after.machine.memory }
  callSupply : after.callSupply = before.callSupply
  grantSupply : after.grantSupply = before.grantSupply
  pending : after.pending = before.pending.erase call
  boundaries : after.boundaries = before.boundaries ++ [.returned call caller agent ids]

theorem return?_effects {Request : Type} {state next : State Request}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    {record : Pending Request}
    (success : return? state call caller agent ids = some (record, next)) :
    ReturnEffects state next call caller agent ids record := by
  have exactBoundary := return?_matches_occurrence success
  have occurrence := exactBoundary.1
  unfold return? at success
  rw [occurrence] at success
  simp only [Option.bind_eq_bind, Option.bind_some] at success
  split at success
  · simp at success
  · cases returned : LoanBatch.return? state.machine.memory caller record.loans with
    | none => simp [returned] at success
    | some memory =>
      simp only [returned, Option.bind_some] at success
      cases checked : checked? { state.machine with memory := memory }
          state.callSupply state.grantSupply (state.pending.erase call)
          (state.boundaries ++ [.returned call caller agent ids]) with
      | none => simp [checked] at success
      | some checkedState =>
        simp only [checked, Option.bind_some] at success
        rcases success with ⟨rfl, rfl⟩
        have fields := checked?_fields checked
        refine ⟨occurrence, exactBoundary.2.1, exactBoundary.2.2.1,
          exactBoundary.2.2.2, ?_, ?_, fields.2.1, fields.2.2.1,
          fields.2.2.2.1, fields.2.2.2.2⟩
        · simpa only [fields.1] using returned
        · rw [fields.1]

/-- `ReturnEffects.unrelated_grant` transports batch framing to the call boundary. -/
theorem ReturnEffects.unrelated_grant {Request : Type} {before after : State Request}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    {record : Pending Request} (effects : ReturnEffects before after call caller agent ids record)
    {id : GrantId} (unrelated : id ∉ record.ids) :
    after.machine.memory.grantAt? id = before.machine.memory.grantAt? id :=
  LoanBatch.grantAt?_return?_unrelated effects.loansReturned unrelated

/-- `ReturnEffects.allocations_unchanged` states that loan return leaves allocation
records, including their byte contents, unchanged. -/
theorem ReturnEffects.allocations_unchanged {Request : Type} {before after : State Request}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    {record : Pending Request} (effects : ReturnEffects before after call caller agent ids record) :
    after.machine.memory.allocations = before.machine.memory.allocations :=
  LoanBatch.allocations_return? effects.loansReturned

/-- `return?_loans_removed` exposes exact loan consumption through the protocol. -/
theorem return?_loans_removed {Request : Type} {state next : State Request}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    {record : Pending Request}
    (success : return? state call caller agent ids = some (record, next)) :
    ∀ id ∈ record.ids, next.machine.memory.grantAt? id = none := by
  have effects := return?_effects success
  have present := FiniteMap.mem_of_lookup effects.occurrence
  have distinct := (state.pendingValid.2 (call, record) present).2.1
  intro id member
  obtain ⟨entry, loanPresent, rfl⟩ := List.mem_map.mp member
  exact LoanBatch.grantAt?_return?_of_mem distinct effects.loansReturned loanPresent

/-- A successful return removes its occurrence from the pending table. -/
theorem return?_removes_pending {Request : Type} {state next : State Request}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    {record : Pending Request}
    (success : return? state call caller agent ids = some (record, next)) :
    next.pending.lookup call = none := by
  unfold return? at success
  cases lookup : state.pending.lookup call with
  | none => simp [lookup] at success
  | some found =>
      simp only [lookup, Option.bind_eq_bind, Option.bind_some] at success
      split at success
      · simp at success
      · cases returned : LoanBatch.return? state.machine.memory caller found.loans with
        | none => simp [returned] at success
        | some memory =>
            simp only [returned, Option.bind_some] at success
            cases checked : checked? { state.machine with memory := memory }
                state.callSupply state.grantSupply (state.pending.erase call)
                (state.boundaries ++ [.returned call caller agent ids]) with
            | none => simp [checked] at success
            | some checkedState =>
                simp only [checked, Option.bind_some] at success
                rcases success with ⟨rfl, rfl⟩
                have fields := checked?_fields checked
                rw [fields.2.2.2.1, FiniteMap.lookup_erase_self]

/-- `return?_replay_rejected` says the same call occurrence cannot return twice. -/
theorem return?_replay_rejected {Request : Type} {state next : State Request}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    {record : Pending Request}
    (success : return? state call caller agent ids = some (record, next)) :
    return? next call caller agent ids = none := by
  have removed := return?_removes_pending success
  simp [return?, removed]

/-- A successful handoff records the freshly minted occurrence, its exact loan
batch, the advanced supplies, and the corresponding boundary. -/
theorem handoff?_records {Request : Type} {state next : State Request}
    {caller agent : ContextId} {request : Request} {loans : List LoanRequest}
    {call : CallId} (success : handoff? state caller agent request loans = some (call, next)) :
    let minted := GrantMint.mint state.grantSupply
      (loans.map (fun loan => loan.grant caller agent))
    call = state.callSupply.fresh.1 ∧
      next.callSupply = state.callSupply.fresh.2 ∧
      next.grantSupply = minted.2 ∧
      next.pending.lookup call = some ⟨caller, agent, request, minted.1⟩ ∧
      next.boundaries = state.boundaries ++
        [.handoff call caller agent (minted.1.map Prod.fst)] ∧
      ∃ memory, LoanBatch.issue? state.machine.memory caller minted.1 = some memory ∧
        next.machine = { state.machine with memory := memory } := by
  dsimp only
  unfold handoff? at success
  split at success
  · simp at success
  · skip
    cases issued : LoanBatch.issue? state.machine.memory caller
        (GrantMint.mint state.grantSupply
          (loans.map fun loan => loan.grant caller agent)).1 with
    | none => simp [issued] at success
    | some memory =>
        simp only [issued, Option.bind_eq_bind, Option.bind_some] at success
        simp only [Pending.ids] at success
        split at success
        · simp at success
        · cases checked : checked? { state.machine with memory := memory }
              state.callSupply.fresh.2
              (GrantMint.mint state.grantSupply
                (loans.map fun loan => loan.grant caller agent)).2
              (state.pending.insert state.callSupply.fresh.1
                ⟨caller, agent, request,
                  (GrantMint.mint state.grantSupply
                    (loans.map fun loan => loan.grant caller agent)).1⟩)
              (state.boundaries ++ [.handoff state.callSupply.fresh.1 caller agent
                ((GrantMint.mint state.grantSupply
                  (loans.map fun loan => loan.grant caller agent)).1.map Prod.fst)]) with
          | none =>
              rw [checked] at success
              simp at success
          | some checkedState =>
              rw [checked] at success
              simp only [Option.bind_some] at success
              rcases success with ⟨rfl, rfl⟩
              have fields := checked?_fields checked
              refine ⟨rfl, fields.2.1, fields.2.2.1, ?_, fields.2.2.2.2, memory,
                rfl, fields.1⟩
              rw [fields.2.2.2.1, FiniteMap.lookup_insert_self]

/-- Successful handoff advances both nominal supplies along their mint histories. -/
theorem handoff?_supplies_reachable {Request : Type} {state next : State Request}
    {caller agent : ContextId} {request : Request} {loans : List LoanRequest}
    {call : CallId} (success : handoff? state caller agent request loans = some (call, next)) :
    FreshSupply.Reachable state.callSupply next.callSupply ∧
      FreshSupply.Reachable state.grantSupply next.grantSupply := by
  have recorded := handoff?_records success
  dsimp only at recorded
  refine ⟨?_, ?_⟩
  · rw [recorded.2.1]
    exact .mint (.refl state.callSupply)
  · rw [recorded.2.2.1]
    exact GrantMint.supply_reachable state.grantSupply
      (loans.map fun loan => loan.grant caller agent)

/-- `step?_of_ran` shows that the invariant check after an authority-free
ordinary step retains the actual machine outcome, including its faults and
violations. -/
theorem step?_of_ran {Request : Type} (state : State Request) (policy : StepPolicy)
    (operation : SomeOperation) (context : ContextId) (kind : ContextKind)
    (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence)
    (machine : MachineState) (notPending : callerPending state context = false)
    (free : authorityFree operation = true)
    (ran : Grass.Op.step policy state.machine operation context kind cause faultAt =
      .ran machine) :
    ∃ next, step? state policy operation context kind cause faultAt = some next ∧
      next.machine = machine ∧ next.callSupply = state.callSupply ∧
      next.grantSupply = state.grantSupply ∧ next.pending = state.pending ∧
      next.boundaries = state.boundaries := by
  have noEffects : ∀ sequence, operation.facets.substeps? = some sequence →
      ∀ access ∈ sequence.accesses, access.authorityEffect = [] := by
    intro sequence sequenceEq access present
    unfold authorityFree at free
    rw [sequenceEq] at free
    simp only [List.all_eq_true] at free
    have empty := free access present
    simpa using empty
  have sameEntries : machine.memory.grantEntries = state.machine.memory.grantEntries :=
    Grass.Op.step_preserves_authority_of_no_effects policy state.machine operation
      context kind cause faultAt machine ran noEffects
  have covered : GrantSupplyCovers machine.memory state.grantSupply := by
    intro entry present
    apply state.grantsCovered entry
    rw [← sameEntries]
    exact present
  have pendingValid : PendingTableValid machine.memory state.callSupply state.pending := by
    refine ⟨state.pendingValid.1, ?_⟩
    intro entry present
    obtain ⟨issued, distinct, holders, matching⟩ := state.pendingValid.2 entry present
    refine ⟨issued, distinct, holders, ?_⟩
    intro loan loanPresent
    rw [MemoryState.grantAt?_eq_of_grantEntries_eq sameEntries]
    exact matching loan loanPresent
  let next : State Request :=
    ⟨machine, state.callSupply, state.grantSupply, state.pending, state.boundaries,
      covered, pendingValid⟩
  refine ⟨next, ?_, rfl, rfl, rfl, rfl, rfl⟩
  unfold step?
  simp only [notPending, Bool.false_eq_true, if_false, free, if_true, ran]
  unfold checked?
  rw [dif_pos covered, dif_pos pendingValid]

end Grass.Op.CallProtocol
