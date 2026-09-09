import Grass.Console.ObservedEmbedding

/-! Literal one-step computation laws for the concrete console embedding. -/

namespace Grass.Console.ObservedEmbedding

open Grass.Std.Logical Grass.Semantics Grass.RelationalSystem
open Grass.Specification Grass.Console Grass.Console.ObservedBehavior

variable {Outcome : Type} (request : LineRequest Outcome) (rendering : LineRendering)

/-- `embedHistory_advance` identifies the entire history after a positive write
step with an append to the embedding of the supplied prior history. -/
theorem embedHistory_advance
    (history : (Behavior.system (Payload request rendering)).History)
    (cut after : OutputCut (Payload request rendering))
    (strict : cut.offset < after.offset) (located : history.state = .pending cut) :
    (embedHistory request rendering
      (history.append (.snoc .nil (Behavior.Choice.reply cut (.advance after strict))
        (Behavior.Event.emitted (cut.between after)) (Behavior.State.pending after) ()
        (by exact ⟨located, rfl, rfl⟩)))).observed =
      (embedHistory request rendering history).observed.append
        (.snoc .nil (ObservedBehavior.Choice.output cut (.advance after strict))
          (ObservedBehavior.Event.emitted (cut.between after))
          (ObservedBehavior.State.writing after) ()
          (by
            have observedLocated :=
              (embedHistory request rendering history).endpoint.pending_observed
                request rendering located
            exact observedLocated ▸ ObservedBehavior.advanceStep request rendering cut after strict)) := by
  cases history with
  | mk initialState initialGraph state graph validInitial path =>
    cases initialGraph
    cases graph
    change initialState = .pending (OutputCut.zero _) at validInitial
    cases validInitial
    cases located
    rfl

/-- `embedHistory_finish` identifies the entire reporting prefix after the
supplied finish, retaining its cut, cause, and selected finish law. -/
theorem embedHistory_finish
    (history : (Behavior.system (Payload request rendering)).History)
    (cut : OutputCut (Payload request rendering)) (cause : Behavior.TerminalCause)
    (allowed : Behavior.FinishAllowed cut cause) (located : history.state = .pending cut) :
    (embedHistory request rendering
      (history.append (.snoc .nil (Behavior.Choice.reply cut (.finish cause))
        (Behavior.Event.terminal cause) (Behavior.State.finished cut cause) ()
        (by exact ⟨located, allowed, rfl, rfl⟩)))).observed =
      (embedHistory request rendering history).observed.append
        (.snoc .nil (ObservedBehavior.Choice.output cut (.finish cause))
          (ObservedBehavior.Event.reported ⟨cut, cause, allowed⟩)
          (ObservedBehavior.State.reporting ⟨cut, cause, allowed⟩) ()
          (by
            have observedLocated :=
              (embedHistory request rendering history).endpoint.pending_observed
                request rendering located
            exact observedLocated ▸
              ObservedBehavior.reportStep request rendering ⟨cut, cause, allowed⟩)) := by
  cases history with
  | mk initialState initialGraph state graph validInitial path =>
    cases initialGraph
    cases graph
    change initialState = .pending (OutputCut.zero _) at validInitial
    cases validInitial
    cases located
    rfl

end Grass.Console.ObservedEmbedding
