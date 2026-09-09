import Grass.Op.CallProtocol
import Grass.Op.CallProtocolCustody
import Tests.Memory.Spike1Policy

/-! Concrete acceptance and refusal checks for occurrence-bound Spike 1 loans. -/

namespace Grass.Tests.CallProtocol

open Grass.Core Grass.Memory Grass.Op Grass.Op.CallProtocol Grass.Std.Logical
open Grass.Tests.Spike1 Tests.Memory.Spike1Block Grass.Tests.Spike1Policy

def machine : MachineState := machine₀.noteContext mainThread .thread

def state₀ : CallProtocol.State Nat :=
  CallProtocol.initial machine FreshSupply.initial (by decide)

def request : Nat := 37

def transferredLoan : LoanRequest :=
  { kind := .loan, provenance := transferredProvenance,
    range := transferredRange, rights := .readWrite }

def fifthArgumentLoan : LoanRequest :=
  { kind := .loan, provenance := fifthArgumentProvenance,
    range := fifthArgumentRange, rights := .readWrite }

def loans : List LoanRequest := [transferredLoan, fifthArgumentLoan]

def handoff := CallProtocol.handoff? state₀ mainThread apiAgent request loans

theorem the_two_loan_handoff_succeeds : handoff.isSome := by decide

theorem an_empty_handoff_succeeds :
    (CallProtocol.handoff? state₀ mainThread apiAgent request []).isSome := by decide

theorem the_handoff_records_exact_live_loans :
    ∀ call pending, handoff = some (call, pending) →
      pending.machine.memory.grantAt? FreshSupply.initial.fresh.1 =
          some (transferredLoan.grant mainThread apiAgent) ∧
      pending.machine.memory.grantAt? FreshSupply.initial.fresh.2.fresh.1 =
          some (fifthArgumentLoan.grant mainThread apiAgent) := by
  intro call pending h
  cases h
  exact ⟨by decide, by decide⟩

theorem the_caller_is_suspended :
    ∀ call pending, handoff = some (call, pending) →
      callerPending pending mainThread = true := by
  intro call pending h
  cases h
  decide

theorem the_exact_return_succeeds_and_returns_the_request :
    ∀ call pending, handoff = some (call, pending) →
      ∃ record returned,
        CallProtocol.return? pending call mainThread apiAgent
          (Option.getD ((pending.pending.lookup call).map Pending.ids) []) =
            some (record, returned) ∧ record.request = request := by
  intro call pending h
  cases h
  refine ⟨_, _, rfl, rfl⟩

theorem the_returned_grants_are_absent_and_the_second_return_is_rejected :
    ∀ call pending record returned,
      handoff = some (call, pending) →
      CallProtocol.return? pending call mainThread apiAgent
        (Option.getD ((pending.pending.lookup call).map Pending.ids) []) = some (record, returned) →
      (∀ id ∈ Pending.ids record, returned.machine.memory.grantAt? id = none) ∧
      CallProtocol.return? returned call mainThread apiAgent (Pending.ids record) = none := by
  intro call pending record returned _hh hr
  refine ⟨CallProtocol.return?_loans_removed hr, ?_⟩
  rw [(CallProtocol.return?_matches_occurrence hr).2.2.2]
  exact CallProtocol.return?_replay_rejected hr

def firstGrant : GrantId := FreshSupply.initial.fresh.1
def secondGrant : GrantId := FreshSupply.initial.fresh.2.fresh.1
def splitLow : GrantId := FreshSupply.initial.fresh.2.fresh.2.fresh.1
def splitHigh : GrantId := FreshSupply.initial.fresh.2.fresh.2.fresh.2.fresh.1

theorem wrong_boundary_claims_are_rejected :
    ∀ call pending, handoff = some (call, pending) →
      CallProtocol.return? pending call apiAgent apiAgent
        (Option.getD ((pending.pending.lookup call).map Pending.ids) []) = none ∧
      CallProtocol.return? pending call mainThread mainThread
        (Option.getD ((pending.pending.lookup call).map Pending.ids) []) = none ∧
      CallProtocol.return? pending call mainThread apiAgent [] = none ∧
      CallProtocol.return? pending call mainThread apiAgent [firstGrant] = none ∧
      CallProtocol.return? pending call mainThread apiAgent
        [firstGrant, firstGrant] = none ∧
      CallProtocol.return? pending call mainThread apiAgent
        [firstGrant, secondGrant, splitLow] = none ∧
      CallProtocol.return? pending call mainThread apiAgent
        (Option.getD ((pending.pending.lookup call).map Pending.ids) []).reverse = none ∧
      CallProtocol.return? pending (pending.callSupply.fresh.1) mainThread apiAgent
        (Option.getD ((pending.pending.lookup call).map Pending.ids) []) = none := by
  intro call pending h
  cases h
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem unknown_and_pending_callers_are_rejected :
    CallProtocol.handoff? state₀ apiAgent mainThread request loans = none ∧
    ∀ call pending, handoff = some (call, pending) →
      CallProtocol.handoff? pending mainThread apiAgent request loans = none := by
  refine ⟨by decide, ?_⟩
  intro call pending h
  cases h
  decide

def emptyLoan : LoanRequest := { transferredLoan with range := ⟨0, 0⟩ }

/-- Failure of the second issue yields `none`, so no partial batch state is published. -/
theorem a_bad_second_loan_exposes_no_partial_batch :
    CallProtocol.handoff? state₀ mainThread apiAgent request
      [transferredLoan, emptyLoan] = none := by decide

inductive BoundaryOp where
  | splitJoin

def exactGrant : AuthorityGrant := transferredLoan.grant mainThread apiAgent
def splitBoundary : Nat := transferredRange.start + 1

instance : HasOperationFacets BoundaryOp where
  facets
    | .splitJoin =>
        { memoryEffects := some (.single
            { agentWrite with authorityEffect :=
                [.split firstGrant splitLow splitHigh splitBoundary,
                  .join splitLow splitHigh firstGrant] })
          faults := some [.pageFault, .generalProtection], restartability := some .notRestartable,
          ordering := some .plain }

theorem the_split_join_cycle_is_not_authority_free :
    authorityFree (SomeOperation.of BoundaryOp.splitJoin) = false := by decide

theorem the_underlying_agent_split_join_cycle_runs_and_restores_the_grant :
    ∀ call pending, handoff = some (call, pending) →
      (Grass.Op.step policy pending.machine (SomeOperation.of BoundaryOp.splitJoin)
        apiAgent .externalAgent ⟨⟨"split-join"⟩⟩).state?.isSome ∧
      ∀ ran, Grass.Op.step policy pending.machine (SomeOperation.of BoundaryOp.splitJoin)
          apiAgent .externalAgent ⟨⟨"split-join"⟩⟩ = .ran ran →
        ran.violations.IsEmpty ∧ ran.memory.grantAt? firstGrant = some exactGrant := by
  intro call pending h
  cases h
  refine ⟨by decide, ?_⟩
  intro ran h
  cases h
  exact ⟨by decide, by decide⟩

theorem pending_steps_and_authority_effects_are_rejected :
    ∀ call pending, handoff = some (call, pending) →
      CallProtocol.step? pending policy (SomeOperation.of Spike1Policy.Op.movEcxImm)
        mainThread .thread ⟨⟨"pending-caller"⟩⟩ = none ∧
      CallProtocol.step? pending policy (SomeOperation.of BoundaryOp.splitJoin)
        apiAgent .externalAgent ⟨⟨"boundary-cycle"⟩⟩ = none := by
  intro call pending h
  cases h
  exact ⟨by decide, by decide⟩

private def reached := handoff.get the_two_loan_handoff_succeeds

private def recorded : Pending Nat :=
  (reached.2.pending.lookup reached.1).get (by decide)

private theorem partition : recorded.LoanPartition [transferredLoan] [fifthArgumentLoan] :=
  handoff?_loanPartition (state := state₀) (next := reached.2)
    (caller := mainThread) (agent := apiAgent) (request := request)
    (call := reached.1) (by rfl) (by rfl)

example : partition.semanticEntries =
    [(firstGrant, transferredLoan.grant mainThread apiAgent)] := by rfl

example : partition.additionalEntries =
    [(secondGrant, fifthArgumentLoan.grant mainThread apiAgent)] := by rfl

example : partition.semanticEntries ++ partition.additionalEntries = recorded.loans :=
  partition.entries_append

example : ¬ recorded.LoanPartition [fifthArgumentLoan] [transferredLoan] := by
  intro swapped
  have different : recorded.loans.map Prod.snd ≠
      ([fifthArgumentLoan] ++ [transferredLoan]).map
        (fun loan => loan.grant recorded.caller recorded.agent) := by decide
  exact different swapped.grantsExact

example : CallProtocol.return? reached.2 reached.1 mainThread apiAgent
    (partition.semanticEntries.map Prod.fst) = none := by decide

private def fullyReturned :=
  (CallProtocol.return? reached.2 reached.1 mainThread apiAgent recorded.ids).get (by decide)

example : ∀ id ∈ recorded.ids, fullyReturned.2.machine.memory.grantAt? id = none :=
  CallProtocol.return?_loans_removed (state := reached.2) (call := reached.1)
    (caller := mainThread) (agent := apiAgent) (ids := recorded.ids) (by rfl)

example : fullyReturned.2.pending.lookup reached.1 = none :=
  CallProtocol.return?_removes_pending (state := reached.2) (call := reached.1)
    (caller := mainThread) (agent := apiAgent) (ids := recorded.ids) (by rfl)

end Grass.Tests.CallProtocol
