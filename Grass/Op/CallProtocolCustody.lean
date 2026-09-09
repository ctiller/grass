import Grass.Op.CallProtocol

/-!
# Occurrence-local loan custody

This module partitions the loan entries stored by one pending call into a
semantic prefix and an endpoint-specific suffix. The partition views use
`List.take` and `List.drop`, so they preserve the identities in that stored
record. `handoff?_loanPartition` connects such a record to an actual mint.
-/

namespace Grass.Op.CallProtocol

open Grass.Memory Grass.Std.Logical

namespace Pending

/-- Evidence that one pending record carries the ordered grants of the semantic
and additional loan requests. `LoanPartition.entries_append` and
`LoanPartition.semantic_grants`/`additional_grants` expose the stored partition. -/
structure LoanPartition {Request : Type} (record : Pending Request)
    (semantic additional : List LoanRequest) : Prop where
  grantsExact : record.loans.map Prod.snd =
    (semantic ++ additional).map (fun request => request.grant record.caller record.agent)

namespace LoanPartition

/-- The actual stored prefix assigned to the semantic loan requests;
`semantic_grants` identifies its ordered grants. -/
def semanticEntries {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (_partition : record.LoanPartition semantic additional) : LoanBatch.Entries :=
  record.loans.take semantic.length

/-- The actual stored suffix assigned to the additional loan requests;
`additional_grants` identifies its ordered grants. -/
def additionalEntries {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (_partition : record.LoanPartition semantic additional) : LoanBatch.Entries :=
  record.loans.drop semantic.length

/-- The two computed views concatenate to the complete stored loan batch. -/
theorem entries_append {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) :
    partition.semanticEntries ++ partition.additionalEntries = record.loans :=
  List.take_append_drop semantic.length record.loans

/-- The semantic prefix carries the requested grants in their original order. -/
theorem semantic_grants {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) :
    partition.semanticEntries.map Prod.snd =
      semantic.map (fun request => request.grant record.caller record.agent) := by
  unfold semanticEntries
  rw [List.map_take, partition.grantsExact, List.map_append]
  simp

/-- The additional suffix carries the requested grants in their original order. -/
theorem additional_grants {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) :
    partition.additionalEntries.map Prod.snd =
      additional.map (fun request => request.grant record.caller record.agent) := by
  unfold additionalEntries
  rw [List.map_drop, partition.grantsExact, List.map_append]
  simp

/-- The semantic view has exactly one stored entry per semantic request. -/
@[simp] theorem semanticEntries_length {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) :
    partition.semanticEntries.length = semantic.length := by
  have lengths := congrArg List.length partition.semantic_grants
  simpa using lengths

/-- The additional view has exactly one stored entry per additional request. -/
@[simp] theorem additionalEntries_length {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) :
    partition.additionalEntries.length = additional.length := by
  have lengths := congrArg List.length partition.additional_grants
  simpa using lengths

/-- At each semantic index, the view and full batch contain the same actual ID
paired with the corresponding semantic grant. -/
theorem semanticEntry_at {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) (index : Nat)
    (bounded : index < semantic.length) :
    ∃ id,
      partition.semanticEntries[index]? =
        some (id, (semantic[index]'bounded).grant record.caller record.agent) ∧
      record.loans[index]? =
        some (id, (semantic[index]'bounded).grant record.caller record.agent) := by
  have entryBound : index < partition.semanticEntries.length := by simpa using bounded
  let entry := partition.semanticEntries[index]
  have grantExact : entry.2 =
      (semantic[index]'bounded).grant record.caller record.agent := by
    have atIndex := congrArg (fun grants => grants[index]?) partition.semantic_grants
    simpa [entry, List.getElem?_eq_getElem entryBound, bounded] using atIndex
  have entryExact : entry =
      (entry.1, (semantic[index]'bounded).grant record.caller record.agent) :=
    Prod.ext rfl grantExact
  refine ⟨entry.1, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem entryBound]
    exact congrArg some entryExact
  · have fullBound : index < record.loans.length := by
      have totalLength := congrArg List.length partition.grantsExact
      simp only [List.length_map, List.length_append] at totalLength
      omega
    rw [List.getElem?_eq_getElem fullBound]
    have prefixExact : partition.semanticEntries[index] = record.loans[index] := by
      exact List.getElem_take
    have fullExact : record.loans[index] =
        (entry.1, (semantic[index]'bounded).grant record.caller record.agent) :=
      prefixExact.symm.trans entryExact
    exact congrArg some fullExact

/-- At each additional index, the suffix view and its position in the full batch
contain the same actual ID paired with the corresponding additional grant. -/
theorem additionalEntry_at {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) (index : Nat)
    (bounded : index < additional.length) :
    ∃ id,
      partition.additionalEntries[index]? =
        some (id, (additional[index]'bounded).grant record.caller record.agent) ∧
      record.loans[semantic.length + index]? =
        some (id, (additional[index]'bounded).grant record.caller record.agent) := by
  have entryBound : index < partition.additionalEntries.length := by simpa using bounded
  let entry := partition.additionalEntries[index]
  have grantExact : entry.2 =
      (additional[index]'bounded).grant record.caller record.agent := by
    have atIndex := congrArg (fun grants => grants[index]?) partition.additional_grants
    simpa [entry, List.getElem?_eq_getElem entryBound, bounded] using atIndex
  have entryExact : entry =
      (entry.1, (additional[index]'bounded).grant record.caller record.agent) :=
    Prod.ext rfl grantExact
  refine ⟨entry.1, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem entryBound]
    exact congrArg some entryExact
  · have fullBound : semantic.length + index < record.loans.length := by
      have totalLength := congrArg List.length partition.grantsExact
      simp only [List.length_map, List.length_append] at totalLength
      omega
    rw [List.getElem?_eq_getElem fullBound]
    have suffixExact : partition.additionalEntries[index] =
        record.loans[semantic.length + index] := by
      exact List.getElem_drop
    have fullExact : record.loans[semantic.length + index] =
        (entry.1, (additional[index]'bounded).grant record.caller record.agent) :=
      suffixExact.symm.trans entryExact
    exact congrArg some fullExact

/-- `Pending.Valid` makes every indexed semantic entry a current exact grant. -/
theorem semanticEntry_current {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) {memory : MemoryState}
    (valid : record.Valid memory) (index : Nat) (bounded : index < semantic.length) :
    ∃ id,
      partition.semanticEntries[index]? =
        some (id, (semantic[index]'bounded).grant record.caller record.agent) ∧
      memory.grantAt? id =
        some ((semantic[index]'bounded).grant record.caller record.agent) := by
  obtain ⟨id, selected, full⟩ := partition.semanticEntry_at index bounded
  refine ⟨id, selected, ?_⟩
  exact valid.2.2 _ (List.mem_of_getElem? full)

/-- `Pending.Valid` makes every indexed additional entry a current exact grant. -/
theorem additionalEntry_current {Request : Type} {record : Pending Request}
    {semantic additional : List LoanRequest}
    (partition : record.LoanPartition semantic additional) {memory : MemoryState}
    (valid : record.Valid memory) (index : Nat) (bounded : index < additional.length) :
    ∃ id,
      partition.additionalEntries[index]? =
        some (id, (additional[index]'bounded).grant record.caller record.agent) ∧
      memory.grantAt? id =
        some ((additional[index]'bounded).grant record.caller record.agent) := by
  obtain ⟨id, selected, full⟩ := partition.additionalEntry_at index bounded
  refine ⟨id, selected, ?_⟩
  exact valid.2.2 _ (List.mem_of_getElem? full)

end LoanPartition
end Pending

/-- An actual successful handoff and lookup identify the complete pending record,
including the actual minted grant IDs and the caller, agent, and request fields. -/
theorem handoff?_record_eq {Request : Type} {state next : State Request}
    {caller agent : Grass.Core.ContextId} {request : Request}
    {loans : List LoanRequest} {call : CallId} {record : Pending Request}
    (success : handoff? state caller agent request loans = some (call, next))
    (lookup : next.pending.lookup call = some record) :
    record = ⟨caller, agent, request,
      (GrantMint.mint state.grantSupply
        (loans.map (fun loan => loan.grant caller agent))).1⟩ := by
  have recorded := handoff?_records success
  dsimp only at recorded
  exact Option.some.inj (lookup.symm.trans recorded.2.2.2.1)

/-- An actual successful handoff of the concatenated request list gives the
stored pending occurrence its ordered loan partition. -/
theorem handoff?_loanPartition {Request : Type} {state next : State Request}
    {caller agent : Grass.Core.ContextId} {request : Request}
    {semantic additional : List LoanRequest} {call : CallId}
    {record : Pending Request}
    (success : handoff? state caller agent request (semantic ++ additional) =
      some (call, next))
    (lookup : next.pending.lookup call = some record) :
    record.LoanPartition semantic additional := by
  have same := handoff?_record_eq success lookup
  subst record
  constructor
  exact GrantMint.map_snd_mint state.grantSupply
    ((semantic ++ additional).map (fun loan => loan.grant caller agent))

end Grass.Op.CallProtocol
