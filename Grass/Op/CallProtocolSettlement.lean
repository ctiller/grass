import Grass.Op.CallProtocol

/-! Consequences of settling one synchronous call. -/

namespace Grass.Op.CallProtocol

open Grass.Core Grass.Memory Grass.Std.Logical

private theorem findValue_mem {K V : Type} [DecidableEq K]
    {entries : List (K × V)} {key : K} {value : V}
    (found : findValue entries key = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [findValue] at found
  | cons entry rest ih =>
    obtain ⟨entryKey, entryValue⟩ := entry
    by_cases same : entryKey = key
    · subst entryKey
      simp [findValue] at found
      cases found
      exact List.mem_cons_self
    · simp [findValue, same] at found
      exact List.mem_cons_of_mem _ (ih found)

private theorem eraseKey_any_caller_false {Request : Type}
    (entries : List (CallId × Pending Request)) (call : CallId) (caller : ContextId)
    (different : ∀ entry ∈ entries, entry.2.caller ≠ caller) :
    (eraseKey entries call).any
      (fun entry => decide (entry.2.caller = caller)) = false := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨entryCall, entryRecord⟩ := entry
    have head := different (entryCall, entryRecord) List.mem_cons_self
    have tail : ∀ entry ∈ rest, entry.2.caller ≠ caller := by
      intro other member
      exact different other (List.mem_cons_of_mem _ member)
    by_cases same : entryCall = call
    · simp [eraseKey, same, ih tail]
    · simp [eraseKey, same, head, ih tail]

private theorem callerPending_erase_of_entries {Request : Type}
    (entries : List (CallId × Pending Request)) (call : CallId)
    (record : Pending Request) (found : findValue entries call = some record)
    (distinct : entries.Pairwise fun left right => left.2.caller ≠ right.2.caller) :
    (eraseKey entries call).any
      (fun entry => decide (entry.2.caller = record.caller)) = false := by
  induction entries with
  | nil => simp [findValue] at found
  | cons entry rest ih =>
    obtain ⟨entryCall, entryRecord⟩ := entry
    cases distinct with
    | cons different restDistinct =>
      by_cases same : entryCall = call
      · subst entryCall
        simp [findValue] at found
        cases found
        simp only [eraseKey]
        apply eraseKey_any_caller_false rest call record.caller
        intro entry member
        exact Ne.symm (different entry member)
      · have restFound : findValue rest call = some record := by
          simpa [findValue, same] using found
        have tail := ih restFound restDistinct
        have recordMem : (call, record) ∈ rest := findValue_mem restFound
        have headDifferent : entryRecord.caller ≠ record.caller :=
          different (call, record) recordMem
        simp [eraseKey, same, headDifferent, tail]

private theorem callerPending_erase_of_lookup {Request : Type}
    (pending : FiniteMap CallId (Pending Request)) (call : CallId)
    (record : Pending Request) (found : pending.lookup call = some record)
    (distinct : pending.entries.Pairwise fun left right => left.2.caller ≠ right.2.caller) :
    (pending.erase call).entries.any
      (fun entry => decide (entry.2.caller = record.caller)) = false :=
  callerPending_erase_of_entries pending.entries call record found distinct

/-- Returning one actual pending occurrence settles its caller completely.
`PendingTableValid` rules out a second outstanding call for the same caller. -/
theorem return?_callerPending_false {Request : Type} {before after : State Request}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    {record : Pending Request}
    (success : return? before call caller agent ids = some (record, after)) :
    callerPending after caller = false := by
  have effects := return?_effects success
  rw [effects.callerMatches.symm]
  unfold callerPending
  rw [effects.pending]
  exact callerPending_erase_of_lookup before.pending call record effects.occurrence
    before.pendingValid.1

end Grass.Op.CallProtocol
