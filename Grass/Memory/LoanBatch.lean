import Grass.Memory.State

/-!
# Checked batches of authority loans

This module packages a list of already chosen grant identities and grants through
the sealed `MemoryState` doors.  Returning checks the complete expected grant,
not merely its identity, before consuming it.
-/

namespace Grass.Memory.LoanBatch

open Grass.Core

/-- Grant identities paired with the exact grant shapes expected at those identities. -/
abbrev Entries := List (GrantId × AuthorityGrant)

/-- Every listed identity is distinct. -/
def DistinctIds (entries : Entries) : Prop := (entries.map Prod.fst).Nodup

/-- The state contains every listed identity with exactly its listed grant. -/
def Matches (state : MemoryState) (entries : Entries) : Prop :=
  ∀ entry ∈ entries, state.grantAt? entry.1 = some entry.2

/-- Issue the supplied grants in order through the checked authority-effect door. -/
def issue? (state : MemoryState) (actor : ContextId) (entries : Entries) :
    Option MemoryState :=
  state.applyAuthorityEffect? actor
    (entries.map fun entry => .issue entry.1 entry.2)

/-- Return the supplied identities in order, refusing unless each still denotes
the exact grant supplied by the caller. -/
def return? : MemoryState → ContextId → Entries → Option MemoryState
  | state, _, [] => some state
  | state, actor, (id, expected) :: rest =>
      if state.grantAt? id = some expected then
        (state.returnGrant? actor id).bind fun next => return? next actor rest
      else
        none

@[simp] theorem issue?_nil (state : MemoryState) (actor : ContextId) :
    issue? state actor [] = some state := rfl

theorem issue?_cons (state : MemoryState) (actor : ContextId)
    (entry : GrantId × AuthorityGrant) (rest : Entries) :
    issue? state actor (entry :: rest) =
      (state.applyAuthorityDelta? actor (.issue entry.1 entry.2)).bind fun next =>
        issue? next actor rest := rfl

@[simp] theorem return?_nil (state : MemoryState) (actor : ContextId) :
    return? state actor [] = some state := rfl

theorem return?_cons (state : MemoryState) (actor : ContextId)
    (id : GrantId) (expected : AuthorityGrant) (rest : Entries) :
    return? state actor ((id, expected) :: rest) =
      if state.grantAt? id = some expected then
        (state.returnGrant? actor id).bind fun next => return? next actor rest
      else
        none := rfl

private theorem issueDoor_of_delta {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {grant : AuthorityGrant}
    (h : state.applyAuthorityDelta? actor (.issue id grant) = some next) :
    state.issue? id grant = some next := by
  change (if grant.lender ≠ actor then none else state.issue? id grant) = some next at h
  split at h
  · simp at h
  · exact h

theorem grantAt?_issue?_unrelated {state issued : MemoryState} {actor : ContextId}
    {entries : Entries} (h : issue? state actor entries = some issued)
    {other : GrantId} (hunrelated : other ∉ entries.map Prod.fst) :
    issued.grantAt? other = state.grantAt? other := by
  induction entries generalizing state issued with
  | nil => cases h; rfl
  | cons entry rest ih =>
    obtain ⟨id, grant⟩ := entry
    rw [issue?_cons] at h
    cases hd : state.applyAuthorityDelta? actor (.issue id grant) with
    | none => simp [hd] at h
    | some mid =>
      simp only [hd, Option.bind_some] at h
      have hparts : other ≠ id ∧ other ∉ rest.map Prod.fst := by
        simpa only [List.map_cons, List.mem_cons, not_or] using hunrelated
      exact (ih h hparts.2).trans
        (MemoryState.grantAt?_issue?_ne (issueDoor_of_delta hd) hparts.1)

theorem matches_issue? {state issued : MemoryState} {actor : ContextId}
    {entries : Entries} (hdistinct : DistinctIds entries)
    (h : issue? state actor entries = some issued) : Matches issued entries := by
  induction entries generalizing state issued with
  | nil => simp [Matches]
  | cons entry rest ih =>
    obtain ⟨id, grant⟩ := entry
    rw [issue?_cons] at h
    cases hd : state.applyAuthorityDelta? actor (.issue id grant) with
    | none => simp [hd] at h
    | some mid =>
      simp only [hd, Option.bind_some] at h
      have hparts : id ∉ rest.map Prod.fst ∧ DistinctIds rest := by
        simpa [DistinctIds] using hdistinct
      intro entry hmem
      rcases List.mem_cons.mp hmem with hhead | hrest
      · cases hhead
        exact (grantAt?_issue?_unrelated h hparts.1).trans
          (MemoryState.grantAt?_issue?_self (issueDoor_of_delta hd))
      · exact ih hparts.2 h entry hrest

theorem grantAt?_issue?_of_mem {state issued : MemoryState} {actor : ContextId}
    {entries : Entries} (hdistinct : DistinctIds entries)
    (h : issue? state actor entries = some issued)
    {id : GrantId} {grant : AuthorityGrant} (hmem : (id, grant) ∈ entries) :
    issued.grantAt? id = some grant :=
  matches_issue? hdistinct h (id, grant) hmem

theorem allocations_issue? {state issued : MemoryState} {actor : ContextId}
    {entries : Entries} (h : issue? state actor entries = some issued) :
    issued.allocations = state.allocations :=
  MemoryState.allocations_applyAuthorityEffect? h

/-- Issuing a loan batch changes authority only; backing bytes and capacities remain. -/
theorem backings_issue? {state issued : MemoryState} {actor : ContextId}
    {entries : Entries} (h : issue? state actor entries = some issued) :
    issued.backings = state.backings :=
  MemoryState.backings_applyAuthorityEffect? h

theorem grantAt?_return?_unrelated {state returned : MemoryState} {actor : ContextId}
    {entries : Entries} (h : return? state actor entries = some returned)
    {other : GrantId} (hunrelated : other ∉ entries.map Prod.fst) :
    returned.grantAt? other = state.grantAt? other := by
  induction entries generalizing state returned with
  | nil => cases h; rfl
  | cons entry rest ih =>
    obtain ⟨id, grant⟩ := entry
    rw [return?_cons] at h
    split at h
    · next hexact =>
      cases hr : state.returnGrant? actor id with
      | none => simp [hr] at h
      | some mid =>
        simp only [hr, Option.bind_some] at h
        have hparts : other ≠ id ∧ other ∉ rest.map Prod.fst := by
          simpa only [List.map_cons, List.mem_cons, not_or] using hunrelated
        exact (ih h hparts.2).trans
          (MemoryState.grantAt?_returnGrant?_ne hr hparts.1)
    · contradiction

theorem grantAt?_return?_of_mem {state returned : MemoryState} {actor : ContextId}
    {entries : Entries} (hdistinct : DistinctIds entries)
    (h : return? state actor entries = some returned)
    {id : GrantId} {grant : AuthorityGrant} (hmem : (id, grant) ∈ entries) :
    returned.grantAt? id = none := by
  induction entries generalizing state returned with
  | nil => simp at hmem
  | cons entry rest ih =>
    obtain ⟨headId, headGrant⟩ := entry
    rw [return?_cons] at h
    split at h
    · next hexact =>
      cases hr : state.returnGrant? actor headId with
      | none => simp [hr] at h
      | some mid =>
        simp only [hr, Option.bind_some] at h
        have hparts : headId ∉ rest.map Prod.fst ∧ DistinctIds rest := by
          simpa [DistinctIds] using hdistinct
        rcases List.mem_cons.mp hmem with hhead | hrest
        · cases hhead
          exact (grantAt?_return?_unrelated h hparts.1).trans
            (MemoryState.grantAt?_returnGrant?_self hr)
        · apply ih hparts.2 h hrest
    · contradiction

theorem allocations_return? {state returned : MemoryState} {actor : ContextId}
    {entries : Entries} (h : return? state actor entries = some returned) :
    returned.allocations = state.allocations := by
  induction entries generalizing state returned with
  | nil => cases h; rfl
  | cons entry rest ih =>
    obtain ⟨id, grant⟩ := entry
    rw [return?_cons] at h
    split at h
    · cases hr : state.returnGrant? actor id with
      | none => simp [hr] at h
      | some mid =>
        simp only [hr, Option.bind_some] at h
        exact (ih h).trans (MemoryState.allocations_returnGrant? hr)
    · contradiction

/-- Returning an exact loan batch does not mutate backing storage. -/
theorem backings_return? {state returned : MemoryState} {actor : ContextId}
    {entries : Entries} (h : return? state actor entries = some returned) :
    returned.backings = state.backings := by
  induction entries generalizing state returned with
  | nil => cases h; rfl
  | cons entry rest ih =>
    obtain ⟨id, grant⟩ := entry
    rw [return?_cons] at h
    split at h
    · cases hr : state.returnGrant? actor id with
      | none => simp [hr] at h
      | some mid =>
        simp only [hr, Option.bind_some] at h
        exact (ih h).trans (MemoryState.backings_returnGrant? hr)
    · contradiction

end Grass.Memory.LoanBatch
