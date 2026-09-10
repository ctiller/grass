import Grass.Core.CallIdentity
import Grass.Memory.Event

/-!
# Synchronous memory-history order

This module records one small, abstract interpretation of synchronous handoff:
ordinary committed memory events extend only their own context's knowledge;
handoff joins the caller's complete frontier into the agent, and a matched
return joins the agent's complete frontier back into the caller.  The model is
deliberately independent of native CALL/RET semantics and of machine stepping.

Every history observation is checked against the exact stored prefix, including
all event fields.  Synchronization doors therefore cannot install arbitrary
order facts or reinterpret an earlier event through a later memory state.
-/

namespace Grass.Memory.Synchronization

open Grass.Core Grass.Op.CallProtocol

/-- The exact synchronous occurrence retained until its matched return. -/
structure Pending where
  call : CallId
  caller : ContextId
  agent : ContextId
  loanIds : List GrantId
deriving DecidableEq, Repr

/-- A finite program-order frontier and the synchronous occurrences in flight.
The constructor is private: public states start empty and change through the
history, handoff, and return doors below. -/
structure State where
  private mk ::
  /-- The exact memory-event history already incorporated. -/
  history : List MemoryEvent
  /-- Per-context event knowledge.  Each context has at most one supported entry. -/
  frontiers : List (ContextId × List MemoryEvent)
  /-- Every call identity ever admitted, including occurrences already returned. -/
  issued : List CallId
  /-- Full synchronous occurrences awaiting a matched return. -/
  pending : List Pending
deriving DecidableEq

private def lookupFrontier : List (ContextId × List MemoryEvent) → ContextId →
    List MemoryEvent
  | [], _ => []
  | (owner, known) :: rest, context =>
      if owner = context then known else lookupFrontier rest context

private def setFrontier : List (ContextId × List MemoryEvent) → ContextId →
    List MemoryEvent → List (ContextId × List MemoryEvent)
  | [], context, known => [(context, known)]
  | (owner, prior) :: rest, context, known =>
      if owner = context then (context, known) :: rest
      else (owner, prior) :: setFrontier rest context known

private def join (known learned : List MemoryEvent) : List MemoryEvent :=
  known ++ learned.filter (fun event => decide (event ∉ known))

private def lookupPending : List Pending → CallId → Option Pending
  | [], _ => none
  | record :: rest, call =>
      if record.call = call then some record else lookupPending rest call

private def erasePending : List Pending → CallId → List Pending
  | [], _ => []
  | record :: rest, call =>
      if record.call = call then erasePending rest call
      else record :: erasePending rest call

/-- The initial synchronization state contains no event or cross-context order. -/
def State.empty : State := ⟨[], [], [], []⟩

instance : EmptyCollection State := ⟨State.empty⟩

/-- The events currently known to one context. -/
def State.frontier (state : State) (context : ContextId) : List MemoryEvent :=
  lookupFrontier state.frontiers context

/-- The pending synchronous occurrence for `call`, if any. -/
def State.pendingAt? (state : State) (call : CallId) : Option Pending :=
  lookupPending state.pending call

/-- Record one committed memory event.  It extends the exact history and only
the performing context's program-order frontier. -/
def State.record (state : State) (event : MemoryEvent) : State :=
  ⟨state.history ++ [event],
    setFrontier state.frontiers event.context.id (state.frontier event.context.id ++ [event]),
    state.issued, state.pending⟩

/-- Incorporate an exact suffix of committed memory events.  Failure means the
stored history is not a prefix of the supplied full-record history. -/
def State.atHistory? (state : State) (history : List MemoryEvent) : Option State :=
  if state.history.IsPrefix history then
    some ((history.drop state.history.length).foldl State.record state)
  else none

/-- Join the complete caller frontier into the agent and retain the exact
pending synchronous occurrence.  An existing call identity is rejected. -/
def State.handoff? (state : State) (history : List MemoryEvent) (call : CallId)
    (caller agent : ContextId) (ids : List GrantId) : Option State := do
  let current ← state.atHistory? history
  if call ∈ current.issued ∨ (current.pendingAt? call).isSome then none else
    some ⟨current.history,
      setFrontier current.frontiers agent (join (current.frontier agent)
        (current.frontier caller)),
      current.issued ++ [call],
      current.pending ++ [⟨call, caller, agent, ids⟩]⟩

/-- Join the complete agent frontier back into the caller and erase exactly the
matched pending occurrence. -/
def State.returned? (state : State) (history : List MemoryEvent) (call : CallId)
    (caller agent : ContextId) (ids : List GrantId) : Option State := do
  let current ← state.atHistory? history
  let record ← current.pendingAt? call
  if record.caller = caller ∧ record.agent = agent ∧ record.loanIds = ids then
    some ⟨current.history,
      setFrontier current.frontiers caller (join (current.frontier caller)
        (current.frontier agent)),
      current.issued,
      erasePending current.pending call⟩
  else none

/-- Decide whether `earlier` is ordered before a proposed fresh event by the
proposed event's current context frontier.  The full supplied history must extend
the stored prefix, the proposed identity must be fresh for that history, and the
earlier full event record must occur both in that history and in the frontier. -/
def State.ordered (state : State) (history : List MemoryEvent) (fresh : EventId)
    (earlier event : MemoryEvent) : Bool :=
  match state.atHistory? history with
  | none => false
  | some current => decide (
      event.id = fresh ∧
      (∀ prior ∈ history, prior.id ≠ fresh) ∧
      earlier ∈ history ∧
      earlier ∈ current.frontier event.context.id)

@[simp] theorem lookupFrontier_set_self (frontiers : List (ContextId × List MemoryEvent))
    (context : ContextId) (known : List MemoryEvent) :
    lookupFrontier (setFrontier frontiers context known) context = known := by
  induction frontiers with
  | nil => simp [setFrontier, lookupFrontier]
  | cons entry rest ih =>
      obtain ⟨owner, prior⟩ := entry
      by_cases h : owner = context <;> simp [setFrontier, lookupFrontier, h, ih]

theorem lookupFrontier_set_other (frontiers : List (ContextId × List MemoryEvent))
    {changed other : ContextId} (hne : other ≠ changed) (known : List MemoryEvent) :
    lookupFrontier (setFrontier frontiers changed known) other =
      lookupFrontier frontiers other := by
  induction frontiers with
  | nil => simp [setFrontier, lookupFrontier, Ne.symm hne]
  | cons entry rest ih =>
      obtain ⟨owner, prior⟩ := entry
      by_cases hc : owner = changed
      · subst owner; simp [setFrontier, lookupFrontier, Ne.symm hne]
      · by_cases ho : owner = other
        · subst owner; simp [setFrontier, lookupFrontier, hc]
        · simp [setFrontier, lookupFrontier, hc, ho, ih]

@[simp] theorem State.frontier_empty (context : ContextId) :
    State.empty.frontier context = [] := rfl

@[simp] theorem State.history_record (state : State) (event : MemoryEvent) :
    (state.record event).history = state.history ++ [event] := rfl

@[simp] theorem State.frontier_record_self (state : State) (event : MemoryEvent) :
    (state.record event).frontier event.context.id =
      state.frontier event.context.id ++ [event] := by
  exact lookupFrontier_set_self _ _ _

theorem State.frontier_record_other (state : State) (event : MemoryEvent)
    {context : ContextId} (hne : context ≠ event.context.id) :
    (state.record event).frontier context = state.frontier context := by
  exact lookupFrontier_set_other _ hne _

@[simp] theorem State.atHistory?_self (state : State) :
    state.atHistory? state.history = some state := by
  simp [State.atHistory?, List.drop_eq_nil_of_le]

theorem State.atHistory?_eq_none_of_not_prefix (state : State)
    (history : List MemoryEvent) (stale : ¬ state.history.IsPrefix history) :
    state.atHistory? history = none := by
  simp [State.atHistory?, stale]

private theorem history_fold_record (state : State) (suffix : List MemoryEvent) :
    (suffix.foldl State.record state).history = state.history ++ suffix := by
  induction suffix generalizing state with
  | nil => simp
  | cons event rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp

theorem State.history_atHistory? {state next : State} {history : List MemoryEvent}
    (advanced : state.atHistory? history = some next) : next.history = history := by
  unfold State.atHistory? at advanced
  split at advanced
  case isTrue hprefix =>
      simp only [Option.some.injEq] at advanced
      subst next
      rw [history_fold_record]
      obtain ⟨suffix, rfl⟩ := hprefix
      simp
  case isFalse => contradiction

@[simp] theorem State.ordered_empty_history (fresh : EventId)
    (earlier event : MemoryEvent) :
    State.empty.ordered [] fresh earlier event = false := by
  simp [State.ordered, State.atHistory?, State.empty, State.frontier, lookupFrontier]

theorem State.history_handoff? {state next : State} {history : List MemoryEvent}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    (handoff : state.handoff? history call caller agent ids = some next) :
    next.history = history := by
  unfold State.handoff? at handoff
  cases advanced : state.atHistory? history with
  | none => simp [advanced] at handoff
  | some current =>
      have exactHistory := State.history_atHistory? advanced
      simp only [advanced, bind, Option.bind] at handoff
      split at handoff
      · contradiction
      · cases handoff
        exact exactHistory

theorem State.history_returned? {state next : State} {history : List MemoryEvent}
    {call : CallId} {caller agent : ContextId} {ids : List GrantId}
    (returned : state.returned? history call caller agent ids = some next) :
    next.history = history := by
  unfold State.returned? at returned
  cases advanced : state.atHistory? history with
  | none => simp [advanced] at returned
  | some current =>
      have exactHistory := State.history_atHistory? advanced
      simp only [advanced, bind, Option.bind] at returned
      cases found : current.pendingAt? call with
      | none => simp [found] at returned
      | some record =>
          simp only [found] at returned
          by_cases hmatches :
              record.caller = caller ∧ record.agent = agent ∧ record.loanIds = ids
          · simp [hmatches] at returned
            cases returned
            exact exactHistory
          · simp [hmatches] at returned

private theorem mem_join_left {event : MemoryEvent} {known learned : List MemoryEvent}
    (member : event ∈ known) : event ∈ join known learned := by
  exact List.mem_append_left _ member

private theorem mem_join_right {event : MemoryEvent} {known learned : List MemoryEvent}
    (member : event ∈ learned) : event ∈ join known learned := by
  by_cases prior : event ∈ known
  · exact mem_join_left prior
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨member, by simp [prior]⟩)

/-- Recording any event never removes prior context knowledge. -/
theorem State.frontier_mem_record {state : State} {known event : MemoryEvent}
    {context : ContextId} (member : known ∈ state.frontier context) :
    known ∈ (state.record event).frontier context := by
  by_cases same : context = event.context.id
  · subst context
    rw [State.frontier_record_self]
    exact List.mem_append_left _ member
  · rw [State.frontier_record_other state event same]
    exact member

private theorem frontier_mem_fold_record {state : State} {known : MemoryEvent}
    {context : ContextId} (suffix : List MemoryEvent)
    (member : known ∈ state.frontier context) :
    known ∈ (suffix.foldl State.record state).frontier context := by
  induction suffix generalizing state with
  | nil => exact member
  | cons event rest ih =>
      simp only [List.foldl_cons]
      exact ih (State.frontier_mem_record member)

/-- Extending an exact history prefix never removes existing knowledge. -/
theorem State.frontier_mem_atHistory? {state next : State} {history : List MemoryEvent}
    {known : MemoryEvent} {context : ContextId}
    (advanced : state.atHistory? history = some next)
    (member : known ∈ state.frontier context) : known ∈ next.frontier context := by
  unfold State.atHistory? at advanced
  split at advanced
  case isTrue =>
    simp only [Option.some.injEq] at advanced
    subst next
    exact frontier_mem_fold_record _ member
  case isFalse => contradiction

/-- A successful handoff retains the agent's prior knowledge. -/
theorem State.frontier_handoff_agent_of_agent {state next : State}
    {history : List MemoryEvent} {call : CallId} {caller agent : ContextId}
    {ids : List GrantId} {event : MemoryEvent}
    (handoff : state.handoff? history call caller agent ids = some next)
    (known : event ∈ state.frontier agent) : event ∈ next.frontier agent := by
  unfold State.handoff? at handoff
  cases advanced : state.atHistory? history with
  | none => simp [advanced] at handoff
  | some current =>
      have currentKnown := State.frontier_mem_atHistory? advanced known
      simp only [advanced, bind, Option.bind] at handoff
      split at handoff
      · contradiction
      · cases handoff
        change event ∈ lookupFrontier (setFrontier current.frontiers agent
          (join (current.frontier agent) (current.frontier caller))) agent
        rw [lookupFrontier_set_self]
        exact mem_join_left currentKnown

/-- A successful handoff joins the complete caller frontier into the agent. -/
theorem State.frontier_handoff_agent_of_caller {state next : State}
    {history : List MemoryEvent} {call : CallId} {caller agent : ContextId}
    {ids : List GrantId} {event : MemoryEvent}
    (handoff : state.handoff? history call caller agent ids = some next)
    (known : event ∈ state.frontier caller) : event ∈ next.frontier agent := by
  unfold State.handoff? at handoff
  cases advanced : state.atHistory? history with
  | none => simp [advanced] at handoff
  | some current =>
      have currentKnown := State.frontier_mem_atHistory? advanced known
      simp only [advanced, bind, Option.bind] at handoff
      split at handoff
      · contradiction
      · cases handoff
        change event ∈ lookupFrontier (setFrontier current.frontiers agent
          (join (current.frontier agent) (current.frontier caller))) agent
        rw [lookupFrontier_set_self]
        exact mem_join_right currentKnown

/-- A matched return retains the caller's prior knowledge. -/
theorem State.frontier_returned_caller_of_caller {state next : State}
    {history : List MemoryEvent} {call : CallId} {caller agent : ContextId}
    {ids : List GrantId} {event : MemoryEvent}
    (returned : state.returned? history call caller agent ids = some next)
    (known : event ∈ state.frontier caller) : event ∈ next.frontier caller := by
  unfold State.returned? at returned
  cases advanced : state.atHistory? history with
  | none => simp [advanced] at returned
  | some current =>
      have currentKnown := State.frontier_mem_atHistory? advanced known
      simp only [advanced, bind, Option.bind] at returned
      cases found : current.pendingAt? call with
      | none => simp [found] at returned
      | some record =>
          simp only [found] at returned
          split at returned
          · cases returned
            change event ∈ lookupFrontier (setFrontier current.frontiers caller
              (join (current.frontier caller) (current.frontier agent))) caller
            rw [lookupFrontier_set_self]
            exact mem_join_left currentKnown
          · contradiction

/-- A matched return joins the complete agent frontier back into the caller. -/
theorem State.frontier_returned_caller_of_agent {state next : State}
    {history : List MemoryEvent} {call : CallId} {caller agent : ContextId}
    {ids : List GrantId} {event : MemoryEvent}
    (returned : state.returned? history call caller agent ids = some next)
    (known : event ∈ state.frontier agent) : event ∈ next.frontier caller := by
  unfold State.returned? at returned
  cases advanced : state.atHistory? history with
  | none => simp [advanced] at returned
  | some current =>
      have currentKnown := State.frontier_mem_atHistory? advanced known
      simp only [advanced, bind, Option.bind] at returned
      cases found : current.pendingAt? call with
      | none => simp [found] at returned
      | some record =>
          simp only [found] at returned
          split at returned
          · cases returned
            change event ∈ lookupFrontier (setFrontier current.frontiers caller
              (join (current.frontier caller) (current.frontier agent))) caller
            rw [lookupFrontier_set_self]
            exact mem_join_right currentKnown
          · contradiction

end Grass.Memory.Synchronization
