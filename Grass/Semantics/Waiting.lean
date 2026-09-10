import Grass.Semantics.History

/-!
# Protocol-indexed permanent waiting

This carrier is for an isolated process that has transferred agency to one
external request. It adds no transition to the underlying system. A protocol
permission is separate from a model's pending predicate, and every possible
step at a waiting boundary must satisfy the supplied reply interpretation.
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

/-- Interpret a selected protocol at exact occurrence-bearing histories.
`Reply` classifies a transition choice; completeness retains every allowed
dependent result without merging two responses at one occurrence/choice.
Exclusion of internal work requires a faithful supplied reply classification. -/
structure WaitBoundary (system : RelationalSystem Event)
    (protocol : WaitProtocol.{uRequest, uResponse} Request) where
  Occurrence : Type uOccurrence
  request : Occurrence → Request
  Pending : system.History → Occurrence → Prop
  Reply : (occurrence : Occurrence) → protocol.Response (request occurrence) →
    system.Choice → Prop
  reply_unique : ∀ occurrence first second choice,
    Reply occurrence first choice → Reply occurrence second choice → first = second
  nonterminal : ∀ history occurrence, Pending history occurrence →
    ¬ system.Terminal history.state history.graph
  step_reply : ∀ history occurrence, Pending history occurrence →
    ∀ choice event next nextGraph,
    system.Step history.graph history.state choice event next nextGraph →
    ∃ response, protocol.Allowed (request occurrence) response ∧
      Reply occurrence response choice
  reply_step : ∀ history occurrence, Pending history occurrence →
    ∀ response, protocol.Allowed (request occurrence) response →
    ∃ choice event next nextGraph,
      Reply occurrence response choice ∧
      system.Step history.graph history.state choice event next nextGraph

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

/-- Every allowed reply remains possible at the same occurrence even though
permanent nonresponse is also represented. This is not eventual response. -/
theorem reply_possible (waiting : PermanentWait boundary history)
    (response : protocol.Response (boundary.request waiting.occurrence))
    (allowed : protocol.Allowed (boundary.request waiting.occurrence) response) :
    ∃ choice event next nextGraph,
      boundary.Reply waiting.occurrence response choice ∧
      system.Step history.graph history.state choice event next nextGraph :=
  boundary.reply_step history waiting.occurrence waiting.pending response allowed

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
