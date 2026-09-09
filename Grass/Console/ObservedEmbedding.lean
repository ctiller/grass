import Grass.Console.ObservedBehavior

/-! Embedding the existing write component into the observed console model.
`HistoryEmbedding.trace` records the ordered choice/event correspondence for
the supplied history. `terminal_embeds_reporting` and
`embedded_terminal_not_terminal` distinguish component completion from whole
observation. This module supplies no provider or terminal-platform law. -/

namespace Grass.Console.ObservedEmbedding
open Grass.Std.Logical Grass.Semantics Grass.RelationalSystem
open Grass.Specification Grass.Console Grass.Console.ObservedBehavior
variable {Outcome : Type} (request : LineRequest Outcome) (rendering : LineRendering)
abbrev Payload := rendering.bytes request.line

/-- Reachable endpoint correspondence carries the selected finish law. -/
inductive Corresponds : Behavior.State (Payload request rendering) →
    ObservedBehavior.State request rendering → Type where
  | pending (cut) : Corresponds (.pending cut) (.writing cut)
  | finished (cut) (cause) (allowed : Behavior.FinishAllowed cut cause) :
      Corresponds (.finished cut cause) (.reporting ⟨cut, cause, allowed⟩)

theorem Corresponds.pending_observed {component observed cut}
    (corresponds : Corresponds request rendering component observed)
    (origin : component = .pending cut) : observed = .writing cut := by
  cases corresponds <;> cases origin
  rfl

structure FinishedObserved {observed : ObservedBehavior.State request rendering}
    (cut : OutputCut (Payload request rendering)) (cause : Behavior.TerminalCause) where
  allowed : Behavior.FinishAllowed cut cause
  equation : observed = .reporting ⟨cut, cause, allowed⟩

theorem Corresponds.finished_observed {component observed cut cause}
    (corresponds : Corresponds request rendering component observed)
    (origin : component = .finished cut cause) :
    FinishedObserved request rendering (observed := observed) cut cause := by
  cases corresponds <;> cases origin
  exact ⟨_, rfl⟩

/-- Paired trace constructors record each advance and finish in order. -/
inductive TraceMap : List (Behavior.Choice (Payload request rendering)) → List Behavior.Event →
    List (ObservedBehavior.Choice request rendering) →
    List (ObservedBehavior.Event request rendering) → Type where
  | nil : TraceMap [] [] [] []
  | advance {bc be oc oe cut after} (prior : TraceMap bc be oc oe)
      (strict : cut.offset < after.offset) :
      TraceMap (bc ++ [.reply cut (.advance after strict)])
        (be ++ [.emitted (cut.between after)])
        (oc ++ [.output cut (.advance after strict)])
        (oe ++ [.emitted (cut.between after)])
  | finish {bc be oc oe cut cause} (prior : TraceMap bc be oc oe)
      (allowed : Behavior.FinishAllowed cut cause) :
      TraceMap (bc ++ [.reply cut (.finish cause)]) (be ++ [.terminal cause])
        (oc ++ [.output cut (.finish cause)])
        (oe ++ [.reported ⟨cut, cause, allowed⟩])

structure HistoryEmbedding
    (history : (Behavior.system (Payload request rendering)).History) where
  observed : (ObservedBehavior.system request rendering).History
  endpoint : Corresponds request rendering history.state observed.state
  trace : TraceMap request rendering history.path.choices history.path.events
    observed.path.choices observed.path.events

/-- Fold an initialized choice-bearing component path into writing/reporting steps. -/
noncomputable def embedPath {initialState componentState}
    {initialGraph componentGraph : Unit}
    (initial : (Behavior.system (Payload request rendering)).Initial initialState initialGraph)
    (path : (Behavior.system (Payload request rendering)).Path
      initialState initialGraph componentState componentGraph) :
    Σ observed : (ObservedBehavior.system request rendering).History,
      Corresponds request rendering componentState observed.state ×
      TraceMap request rendering path.choices path.events
        observed.path.choices observed.path.events := by
    let motive := fun componentState componentGraph
        (componentPath : (Behavior.system (Payload request rendering)).Path
          initialState initialGraph componentState componentGraph) =>
      Σ observed : (ObservedBehavior.system request rendering).History,
        Corresponds request rendering componentState observed.state ×
        TraceMap request rendering componentPath.choices componentPath.events
          observed.path.choices observed.path.events
    exact Path.rec (motive := motive)
      ⟨ObservedBehavior.initial request rendering,
        initial.symm ▸ .pending (OutputCut.zero _), .nil⟩
      (by
        intro current currentGraph prior choice event next nextGraph step ih
        let observed := ih.1
        let endpoint := ih.2.1
        let trace := ih.2.2
        rcases choice with ⟨cut, response⟩
        cases response with
        | advance after strict =>
          rcases step with ⟨origin, eventEq, nextEq⟩
          subst event; subst next
          cases currentGraph; cases nextGraph
          have observedOrigin := endpoint.pending_observed request rendering origin
          let extended := observed.append (.snoc .nil
            (ObservedBehavior.Choice.output cut (.advance after strict))
            (ObservedBehavior.Event.emitted (cut.between after))
            (ObservedBehavior.State.writing after) ()
            (observedOrigin ▸ ObservedBehavior.advanceStep request rendering cut after strict))
          have extendedState : extended.state = ObservedBehavior.State.writing after := rfl
          exact ⟨extended, extendedState.symm ▸ .pending after, by
            change TraceMap request rendering
              (prior.choices ++ [.reply cut (.advance after strict)])
              (prior.events ++ [.emitted (cut.between after)])
              (observed.path.choices ++ [.output cut (.advance after strict)])
              (observed.path.events ++ [.emitted (cut.between after)])
            exact TraceMap.advance trace strict⟩
        | finish cause =>
          rcases step with ⟨origin, allowed, eventEq, nextEq⟩
          subst event; subst next
          cases currentGraph; cases nextGraph
          have observedOrigin := endpoint.pending_observed request rendering origin
          let selection : Selection request rendering := ⟨cut, cause, allowed⟩
          let extended := observed.append (.snoc .nil
            (ObservedBehavior.Choice.output cut (.finish cause))
            (ObservedBehavior.Event.reported selection)
            (ObservedBehavior.State.reporting selection) ()
            (observedOrigin ▸ ObservedBehavior.reportStep request rendering selection))
          have extendedState : extended.state = ObservedBehavior.State.reporting selection := rfl
          exact ⟨extended, extendedState.symm ▸ .finished cut cause allowed, by
            change TraceMap request rendering
              (prior.choices ++ [.reply cut (.finish cause)])
              (prior.events ++ [.terminal cause])
              (observed.path.choices ++ [.output cut (.finish cause)])
              (observed.path.events ++ [.reported selection])
            exact TraceMap.finish trace allowed⟩)
      path

/-- Fold the supplied choice-bearing component history into an exact observed prefix. -/
noncomputable def embedHistory (history : (Behavior.system (Payload request rendering)).History) :
    HistoryEmbedding request rendering history := by
  let built := embedPath request rendering history.validInitial history.path
  exact ⟨built.1, built.2.1, built.2.2⟩

/-- Transfer the same output cut's nonresponse to the embedded reached history. -/
noncomputable def embedPermanentWait {history : (Behavior.system (Payload request rendering)).History}
    (waiting : PermanentWait (Behavior.boundary (Payload request rendering)) history) :
    PermanentWait (ObservedBehavior.boundary request rendering)
      (embedHistory request rendering history).observed := by
  rcases waiting with ⟨cut, pending, permitted⟩
  have endpoint := (embedHistory request rendering history).endpoint
  have observedPending := endpoint.pending_observed request rendering pending
  exact ⟨.output cut, observedPending, permitted⟩

/-- The wait transfer retains the original output occurrence. -/
@[simp] theorem embedPermanentWait_occurrence
    {history : (Behavior.system (Payload request rendering)).History}
    (waiting : PermanentWait (Behavior.boundary (Payload request rendering)) history) :
    (embedPermanentWait request rendering waiting).occurrence = .output waiting.occurrence := by
  cases waiting
  rfl

theorem terminal_embeds_reporting {history : (Behavior.system (Payload request rendering)).History}
    (terminal : (Behavior.system (Payload request rendering)).Terminal history.state history.graph) :
    ∃ selection, (embedHistory request rendering history).observed.state = .reporting selection := by
  rcases terminal with ⟨cut, cause, stateEq, allowed⟩
  have endpoint := (embedHistory request rendering history).endpoint
  let reached := endpoint.finished_observed request rendering stateEq
  exact ⟨⟨cut, cause, reached.allowed⟩, reached.equation⟩

theorem embedded_terminal_not_terminal {history : (Behavior.system (Payload request rendering)).History}
    (terminal : (Behavior.system (Payload request rendering)).Terminal history.state history.graph) :
    ¬ (ObservedBehavior.system request rendering).Terminal
      (embedHistory request rendering history).observed.state () := by
  obtain ⟨selection, reporting⟩ := terminal_embeds_reporting request rendering terminal
  rw [reporting]
  simp [ObservedBehavior.system]

theorem observeEmbeddedTerminal {history : (Behavior.system (Payload request rendering)).History}
    (terminal : (Behavior.system (Payload request rendering)).Terminal history.state history.graph) :
    Nonempty (TerminalExtension (ObservedBehavior.boundary request rendering)
      (embedHistory request rendering history).observed) := by
  obtain ⟨selection, reporting⟩ := terminal_embeds_reporting request rendering terminal
  let suffix : (ObservedBehavior.system request rendering).Path
      (embedHistory request rendering history).observed.state
      (embedHistory request rendering history).observed.graph (.observed selection) () :=
    .snoc (Path.nil : (ObservedBehavior.system request rendering).Path
      (embedHistory request rendering history).observed.state
      (embedHistory request rendering history).observed.graph
      (embedHistory request rendering history).observed.state
      (embedHistory request rendering history).observed.graph)
    (ObservedBehavior.Choice.observe selection ()) (ObservedBehavior.Event.observed selection)
    (ObservedBehavior.State.observed selection) ()
    (by cases (embedHistory request rendering history).observed.graph
        exact reporting ▸ ObservedBehavior.observeStep request rendering selection)
  exact ⟨⟨.observed selection, (), suffix, ⟨selection, rfl⟩⟩⟩

/-- The bounded source component has no infinite step stream; this is an
impossibility proof, not a terminal replacement for a divergent behavior. -/
theorem component_infinite_impossible {state : Behavior.State (Payload request rendering)} {priorEvents}
    (continuation : (Behavior.system (Payload request rendering)).InfiniteContinuation state () priorEvents) :
    False := Console.Accounting.no_infinite_continuation continuation
end Grass.Console.ObservedEmbedding
