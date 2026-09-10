import Grass.Semantics.History

/-!
# Protocol-indexed permanent waiting

This carrier is for an isolated process that has transferred agency to one
external request. It adds no transition to the underlying system. A protocol
permission is separate from a model's pending predicate, and every possible
step at a waiting boundary must require the selected external agency. An actual
reply can follow a finite service path whose choices and observations remain.
That interpretation's connection to actual external delivery is a separate
model-to-protocol obligation; a predicate named `Reply` cannot establish it.
Concurrent activity
in other processes needs a richer boundary interpretation.

The protocol is an explicit index, not an inferred property of pending loans.
The eventual authoritative-contract certificate must capture this exact value;
this module does not connect a caller-selected protocol to `SpecProcess`.
Finite observations, silent infinite executions, and permanent waits are not
identified, and no fairness or responsiveness assumption is imposed.
-/

namespace Grass

universe uSystem uRequest uResponse uOccurrence

/-- The selected external request/response law and its nonresponse permission. -/
structure WaitProtocol (Request : Type uRequest) where
  Response : Request → Type uResponse
  Allowed : (request : Request) → Response request → Prop
  AllowsPermanentWait : Request → Prop

namespace RelationalSystem

variable {Event : Type uSystem} {Request : Type uRequest}
  {system : RelationalSystem Event}

/-- Interpret external agency and completed replies at exact histories.
Every enabled step at a pending cut requires the selected external agency;
service steps can retain the occurrence before a later actual reply. The
meaning of `External` is a fixed model/profile obligation, not inferred from
an actor's name. Reply realization retains the existing choice-bearing Path. -/
structure WaitBoundary (system : RelationalSystem Event)
    (protocol : WaitProtocol.{uRequest, uResponse} Request) where
  Occurrence : Type uOccurrence
  request : Occurrence → Request
  Pending : system.History → Occurrence → Prop
  External : Occurrence → system.Choice → Prop
  Reply : (occurrence : Occurrence) → protocol.Response (request occurrence) →
    system.Choice → Prop
  reply_unique : ∀ occurrence first second choice,
    Reply occurrence first choice → Reply occurrence second choice → first = second
  nonterminal : ∀ history occurrence, Pending history occurrence →
    ¬ system.Terminal history.state history.graph
  step_external : ∀ history occurrence, Pending history occurrence →
    ∀ choice event next nextGraph,
    system.Step history.graph history.state choice event next nextGraph →
      External occurrence choice
  step_pending_or_reply : ∀ history occurrence, Pending history occurrence →
    ∀ choice event next nextGraph,
    ∀ step : system.Step history.graph history.state choice event next nextGraph,
      Pending (history.append (.snoc .nil choice event next nextGraph step)) occurrence ∨
      ∃ response, protocol.Allowed (request occurrence) response ∧
        Reply occurrence response choice
  reply_allowed : ∀ history occurrence, Pending history occurrence →
    ∀ response choice event next nextGraph,
    system.Step history.graph history.state choice event next nextGraph →
    Reply occurrence response choice → protocol.Allowed (request occurrence) response
  reply_ends : ∀ history occurrence, Pending history occurrence →
    ∀ response choice event next nextGraph,
    ∀ step : system.Step history.graph history.state choice event next nextGraph,
    Reply occurrence response choice →
      ¬ Pending (history.append (.snoc .nil choice event next nextGraph step)) occurrence
  reply_path : ∀ history occurrence, Pending history occurrence →
    ∀ response, protocol.Allowed (request occurrence) response →
    ∃ state graph, ∃ beforeReply : system.Path history.state history.graph state graph,
      (∀ choice ∈ beforeReply.choices, ∀ earlier, ¬ Reply occurrence earlier choice) ∧
      Pending (history.append beforeReply) occurrence ∧
      ∃ choice event next nextGraph,
        Reply occurrence response choice ∧
        system.Step graph state choice event next nextGraph
namespace WaitBoundary

variable {protocol : WaitProtocol.{uRequest, uResponse} Request}
  (boundary : system.WaitBoundary.{uSystem, uRequest, uResponse, uOccurrence} protocol)

/-- `path_pending_or_reply` follows the actual path: either this occurrence is
still pending, or one of its retained choices delivered an allowed reply. -/
theorem path_pending_or_reply (history : system.History) (occurrence : boundary.Occurrence)
    (pending : boundary.Pending history occurrence) {state graph}
    (path : system.Path history.state history.graph state graph) :
    boundary.Pending (history.append path) occurrence ∨
      ∃ response choice, protocol.Allowed (boundary.request occurrence) response ∧
        boundary.Reply occurrence response choice ∧ choice ∈ path.choices := by
  induction path with
  | nil => exact Or.inl pending
  | @snoc state graph prior choice event next nextGraph step ih =>
      rcases ih with still | ⟨response, actual, allowed, reply, member⟩
      · rcases boundary.step_pending_or_reply (history.append prior) occurrence still
          choice event next nextGraph step with retained | ⟨response, allowed, reply⟩
        · exact Or.inl retained
        · exact Or.inr ⟨response, choice, allowed, reply, by simp [Path.choices]⟩
      · exact Or.inr ⟨response, actual, allowed, reply,
          List.mem_append_left _ member⟩

/-- `pending_of_no_reply_path` retains the same occurrence through every
actual finite prefix containing no reply for it. -/
theorem pending_of_no_reply_path (history : system.History)
    (occurrence : boundary.Occurrence) (pending : boundary.Pending history occurrence)
    {state graph} (path : system.Path history.state history.graph state graph)
    (noReply : ∀ choice ∈ path.choices, ∀ response, ¬ boundary.Reply occurrence response choice) :
    boundary.Pending (history.append path) occurrence := by
  rcases boundary.path_pending_or_reply history occurrence pending path with retained |
    ⟨response, choice, _, reply, member⟩
  · exact retained
  · exact False.elim (noReply choice member response reply)

/-- `external_of_no_reply_path` classifies every retained service choice using
its actual intermediate pending history and the all-step agency law. -/
theorem external_of_no_reply_path (history : system.History)
    (occurrence : boundary.Occurrence) (pending : boundary.Pending history occurrence)
    {state graph} (path : system.Path history.state history.graph state graph)
    (noReply : ∀ choice ∈ path.choices, ∀ response, ¬ boundary.Reply occurrence response choice) :
    ∀ choice ∈ path.choices, boundary.External occurrence choice := by
  induction path with
  | nil => simp [Path.choices]
  | @snoc state graph prior selected event next nextGraph step ih =>
    have priorFree : ∀ choice ∈ prior.choices, ∀ response,
        ¬ boundary.Reply occurrence response choice := by
      intro choice member response
      exact noReply choice (List.mem_append_left _ member) response
    intro choice member
    rcases List.mem_append.mp member with old | last
    · exact ih priorFree choice old
    · have same : choice = selected := by simpa using last
      subst choice
      exact boundary.step_external (history.append prior) occurrence
        (boundary.pending_of_no_reply_path history occurrence pending prior priorFree)
        selected event next nextGraph step
/-- `terminal_has_reply` excludes a terminal endpoint while this occurrence
remains pending, so a terminal path must retain an actual allowed reply. -/
theorem terminal_has_reply (history : system.History) (occurrence : boundary.Occurrence)
    (pending : boundary.Pending history occurrence) {state graph}
    (path : system.Path history.state history.graph state graph)
    (terminal : system.Terminal state graph) :
    ∃ response choice, protocol.Allowed (boundary.request occurrence) response ∧
      boundary.Reply occurrence response choice ∧ choice ∈ path.choices := by
  rcases boundary.path_pending_or_reply history occurrence pending path with retained | replied
  · exact False.elim (boundary.nonterminal (history.append path) occurrence retained terminal)
  · exact replied

end WaitBoundary
/-- A permanent wait holds the exact existing occurrence without taking a
step, delivering a result, changing custody, or creating a replacement. -/
structure PermanentWait {protocol : WaitProtocol.{uRequest, uResponse} Request}
    (boundary : system.WaitBoundary.{uSystem, uRequest, uResponse, uOccurrence} protocol)
    (history : system.History) where
  occurrence : boundary.Occurrence
  pending : boundary.Pending history occurrence
  permitted : protocol.AllowsPermanentWait (boundary.request occurrence)

namespace PermanentWait

variable {protocol : WaitProtocol.{uRequest, uResponse} Request}
  {boundary : system.WaitBoundary.{uSystem, uRequest, uResponse, uOccurrence} protocol}
  {history : system.History}

/-- `WaitBoundary.nonterminal` excludes a terminal boundary from permanent waits. -/
theorem not_terminal (waiting : PermanentWait boundary history) :
    ¬ system.Terminal history.state history.graph :=
  boundary.nonterminal history waiting.occurrence waiting.pending

/-- `PermanentWait.permitted` excludes waits when the selected protocol forbids them. -/
theorem impossible_when_forbidden
    (forbidden : ∀ occurrence, boundary.Pending history occurrence →
      ¬ protocol.AllowsPermanentWait (boundary.request occurrence)) :
    ¬ Nonempty (PermanentWait boundary history) := by
  rintro ⟨waiting⟩
  exact forbidden waiting.occurrence waiting.pending waiting.permitted

/-- Every allowed reply has an actual finite service path followed by its
completed response. Permanent nonresponse itself takes no step. -/
theorem reply_possible (waiting : PermanentWait boundary history)
    (response : protocol.Response (boundary.request waiting.occurrence))
    (allowed : protocol.Allowed (boundary.request waiting.occurrence) response) :
    ∃ state graph, ∃ beforeReply : system.Path history.state history.graph state graph,
      (∀ choice ∈ beforeReply.choices, ∀ earlier,
        ¬ boundary.Reply waiting.occurrence earlier choice) ∧
      boundary.Pending (history.append beforeReply) waiting.occurrence ∧
      ∃ choice event next nextGraph,
        boundary.Reply waiting.occurrence response choice ∧
        system.Step graph state choice event next nextGraph :=
  boundary.reply_path history waiting.occurrence waiting.pending response allowed
end PermanentWait

/-- Complete histories keep terminal, infinite-step, and external nonresponse
forms distinct. An infinite suffix retains the existing graph consistency law
and is attached to the exact choice-bearing finite history. That existing law
sees prior finite events, not prior finite choices; this carrier does not add a
stronger history-sensitive infinite-admissibility condition. -/
inductive CompleteHistory {protocol : WaitProtocol.{uRequest, uResponse} Request}
    (boundary : system.WaitBoundary.{uSystem, uRequest, uResponse, uOccurrence} protocol) :
    Type (max uSystem uRequest uResponse uOccurrence) where
  | terminal (history : system.History)
      (finished : system.Terminal history.state history.graph)
  | infinite (history : system.History)
      (continuation : system.InfiniteContinuation history.state history.graph history.path.events)
  | waiting (history : system.History) (wait : PermanentWait boundary history)

end RelationalSystem
end Grass
