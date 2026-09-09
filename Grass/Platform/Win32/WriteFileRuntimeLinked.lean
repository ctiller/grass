import Grass.Platform.Win32.WriteFileRuntime
import Grass.Platform.Win32.WriteFileService

/-!
# Runtime-table domain linkage for `WriteFile`

The service endpoint changes one runtime table entry while preserving the
protocol metadata.  This module proves that it retains the raw-state runtime
domain invariant without assigning ABI validity to that invariant.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86
open Grass.Platform.Win32.ExecutionState

/-- Every entry surviving a raw association-list key erasure was an entry of
the original list.  This speaks about list membership, not lookup, because a
finite map may contain shadowed entries. -/
private theorem mem_of_mem_eraseKey {K V : Type} [DecidableEq K]
    (entries : List (K × V)) (key : K) (entry : K × V) :
    entry ∈ eraseKey entries key → entry ∈ entries := by
  induction entries with
  | nil => simp
  | cons head rest ih =>
      obtain ⟨headKey, headValue⟩ := head
      by_cases same : headKey = key
      · simp only [eraseKey, same, ↓reduceIte]
        intro member
        exact List.mem_cons.mpr (Or.inr (ih member))
      · intro member
        simp only [eraseKey, same] at member
        rcases List.mem_cons.mp member with equal | member
        · exact List.mem_cons.mpr (Or.inl equal)
        · exact List.mem_cons.mpr (Or.inr (ih member))

/-- An entry surviving `eraseKey` cannot retain the erased key. -/
private theorem key_ne_of_mem_eraseKey {K V : Type} [DecidableEq K]
    (entries : List (K × V)) (key : K) {entry : K × V} :
    entry ∈ eraseKey entries key → entry.1 ≠ key := by
  induction entries with
  | nil => simp
  | cons head rest ih =>
      obtain ⟨headKey, headValue⟩ := head
      by_cases same : headKey = key
      · simp only [eraseKey, same, ↓reduceIte]
        exact ih
      · intro member entryKey
        simp only [eraseKey, same] at member
        rcases List.mem_cons.mp member with equal | member
        · cases equal
          exact same entryKey
        · exact ih member entryKey

/-- `ServiceReceipt.runtimeLinked` proves runtime-table linkage: every runtime
entry has a matching protocol occurrence and every pending occurrence has a
runtime lookup.  The proof uses the actual runtime lookup and the exact
metadata preservation theorem; it makes no ABI-validity claim. -/
theorem ServiceReceipt.runtimeLinked {realization : Realization} {before : RawState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {action : Action} {output : Vec Byte}
    (receipt : ServiceReceipt realization before call record action output)
    (linked : before.RuntimeLinked) : receipt.after.RuntimeLinked := by
  constructor
  · intro entry member
    obtain ⟨entryCall, runtime⟩ := entry
    change (entryCall, runtime) ∈
      (call, .writeFile receipt.nextRuntime) :: eraseKey before.calls.entries call at member
    rcases List.mem_cons.mp member with current | prior
    · cases current
      refine ⟨embedPending record, ?_, ?_⟩
      · rw [receipt.metadata_unchanged,
          ← (CallProtocol.Metadata.pack?_fields receipt.projected).2]
        exact receipt.pre.pending.lookup
      · trivial
    · obtain ⟨pending, pendingLookup, runtimeMatches⟩ := linked.1 (entryCall, runtime)
        (mem_of_mem_eraseKey before.calls.entries call (entryCall, runtime) prior)
      refine ⟨pending, ?_, runtimeMatches⟩
      rw [receipt.metadata_unchanged]
      exact pendingLookup
  · intro entry member
    obtain ⟨pendingCall, pending⟩ := entry
    have priorMember : (pendingCall, pending) ∈ before.metadata.pending.entries := by
      rw [← receipt.metadata_unchanged]
      exact member
    obtain ⟨runtime, runtimeLookup⟩ := linked.2 (pendingCall, pending) priorMember
    by_cases current : pendingCall = call
    · subst pendingCall
      exact ⟨.writeFile receipt.nextRuntime, receipt.after_runtimeLookup⟩
    · exact ⟨runtime, receipt.after_otherCall current |>.trans runtimeLookup⟩

/-- `CallHandoff.rawAfter_runtimeLinked` proves that the actual full-batch handoff initializes the new runtime-table entry and
preserves every pre-existing runtime/pending correspondence. -/
theorem CallHandoff.rawAfter_runtimeLinked {image : Loader.ImageInput}
    {inputs : Loader.EntryInputs} {loaded : Loader.LoadedImage image inputs}
    {before : ExecutionState.State ApiRequest} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable)
    (linked : (before.raw prior).RuntimeLinked) : (handoff.rawAfter prior).RuntimeLinked := by
  have reached := reachedCall?_fields handoff.reachedExact
  have projected := ExecutionState.State.callProtocol?_fields handoff.handoff.projected
  have beforeMetadata : handoff.handoff.beforeProtocol.metadata = before.metadata :=
    projected.2.trans reached.2.1
  have pendingUpdate := CallProtocol.handoff?_pending handoff.handoff.issued
  have fresh := CallProtocol.handoff?_fresh handoff.handoff.issued
  constructor
  · intro entry member
    obtain ⟨entryCall, runtime⟩ := entry
    change (entryCall, runtime) ∈ (handoff.handoff.call, .writeFile handoff.runtime) ::
      eraseKey prior.entries handoff.handoff.call at member
    rcases List.mem_cons.mp member with current | priorMember
    · cases current
      refine ⟨embedPending handoff.handoff.record, ?_, trivial⟩
      change handoff.handoff.afterProtocol.pending.lookup handoff.handoff.call =
        some (embedPending handoff.handoff.record)
      rw [pendingUpdate]
      rw [FiniteMap.lookup_insert_self]
      rfl
    · obtain ⟨pending, pendingLookup, runtimeMatches⟩ := linked.1 (entryCall, runtime)
        (mem_of_mem_eraseKey prior.entries handoff.handoff.call (entryCall, runtime) priorMember)
      have protocolLookup : handoff.handoff.beforeProtocol.pending.lookup entryCall = some pending := by
        change handoff.handoff.beforeProtocol.metadata.pending.lookup entryCall = some pending
        rw [beforeMetadata]
        exact pendingLookup
      have different : entryCall ≠ handoff.handoff.call := by
        intro same
        subst entryCall
        rw [fresh] at protocolLookup
        contradiction
      refine ⟨pending, ?_, runtimeMatches⟩
      change handoff.handoff.afterProtocol.pending.lookup entryCall = some pending
      rw [pendingUpdate, FiniteMap.lookup_insert_ne _ different]
      exact protocolLookup
  · intro entry member
    obtain ⟨pendingCall, pending⟩ := entry
    change (pendingCall, pending) ∈ handoff.handoff.afterProtocol.pending.entries at member
    rw [pendingUpdate] at member
    change (pendingCall, pending) ∈
      (handoff.handoff.call, embedPending handoff.handoff.record) ::
        eraseKey handoff.handoff.beforeProtocol.pending.entries handoff.handoff.call at member
    rcases List.mem_cons.mp member with current | priorMember
    · cases current
      exact ⟨.writeFile handoff.runtime, handoff.rawAfter_lookup prior⟩
    · have different := key_ne_of_mem_eraseKey handoff.handoff.beforeProtocol.pending.entries
        handoff.handoff.call priorMember
      have beforeMember : (pendingCall, pending) ∈ before.metadata.pending.entries := by
        rw [← beforeMetadata]
        exact mem_of_mem_eraseKey handoff.handoff.beforeProtocol.pending.entries
          handoff.handoff.call (pendingCall, pending) priorMember
      obtain ⟨runtime, runtimeLookup⟩ := linked.2 (pendingCall, pending) beforeMember
      refine ⟨runtime, ?_⟩
      exact (handoff.rawAfter_other prior different).trans runtimeLookup

/-- `CallHandoff.runtimeFresh` proves that the actual call identity is absent from the supplied runtime table before
handoff, so the computed insertion cannot overwrite an existing runtime. -/
theorem CallHandoff.runtimeFresh {image : Loader.ImageInput}
    {inputs : Loader.EntryInputs} {loaded : Loader.LoadedImage image inputs}
    {before : ExecutionState.State ApiRequest} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {agent : ContextId}
    (handoff : CallHandoff loaded before receipt request agent) (prior : CallRuntimeTable)
    (linked : (before.raw prior).RuntimeLinked) : prior.lookup handoff.handoff.call = none := by
  have reached := reachedCall?_fields handoff.reachedExact
  have projected := ExecutionState.State.callProtocol?_fields handoff.handoff.projected
  have beforeMetadata : handoff.handoff.beforeProtocol.metadata = before.metadata :=
    projected.2.trans reached.2.1
  have fresh := CallProtocol.handoff?_fresh handoff.handoff.issued
  cases found : prior.lookup handoff.handoff.call with
  | none => rfl
  | some runtime =>
      obtain ⟨pending, pendingLookup, _⟩ := linked.1 (handoff.handoff.call, runtime)
        (FiniteMap.mem_of_lookup found)
      have protocolLookup : handoff.handoff.beforeProtocol.pending.lookup handoff.handoff.call =
          some pending := by
        change handoff.handoff.beforeProtocol.metadata.pending.lookup handoff.handoff.call =
          some pending
        rw [beforeMetadata]
        exact pendingLookup
      rw [fresh] at protocolLookup
      contradiction

end Grass.Platform.Win32.WriteFile
