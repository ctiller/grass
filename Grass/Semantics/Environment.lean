import Grass.Semantics.BehaviorModel

/-!
# Standard environment responsiveness for complete behavior models

`EnvironmentStrategy.Compatible` retains every terminal and infinite
continuation and consults timing permission for permanent waits. Difficult result values,
internal choices, terminal suffixes, and productive infinite executions are
retained by construction.
-/

namespace Grass

namespace BehaviorModel

universe uSystem uRequest uResponse uOccurrence

variable {Outcome : Type}
  (model : BehaviorModel.{uSystem, uRequest, uResponse, uOccurrence} Outcome)

/-- A maximal continuation beginning at one exact choice-bearing history. -/
inductive MaximalContinuation (history : model.History) :
    Type (max uSystem uRequest uResponse uOccurrence) where
  | terminal {state graph}
      (path : model.system.Path history.state history.graph state graph)
      (finished : model.system.Terminal state graph)
  | infinite
      (continuation : model.system.InfiniteContinuation history.state history.graph
        history.path.events)
  | waiting {state graph}
      (path : model.system.Path history.state history.graph state graph)
      (wait : RelationalSystem.PermanentWait model.boundary (history.append path))

/-- `EnvironmentStrategy.Compatible` consults this strategy for permanent waits;
its terminal and infinite cases are unconditional. -/
structure EnvironmentStrategy where
  permitsNonresponseAt : model.History → model.boundary.Occurrence → Prop

namespace EnvironmentStrategy

/-- This timing strategy excludes stationary permanent waits. Proving actual
responsiveness additionally requires replies on its retained infinite runs. -/
def responding : model.EnvironmentStrategy where
  permitsNonresponseAt := fun _ _ => False

/-- The base timing strategy retains every protocol-permitted permanent wait. -/
def unrestricted : model.EnvironmentStrategy where
  permitsNonresponseAt := fun _ _ => True

/-- Permission specialized to an actual protocol-permitted wait witness. -/
def permitsNonresponse (strategy : model.EnvironmentStrategy)
    (history : model.History) (wait : RelationalSystem.PermanentWait model.boundary history) : Prop :=
  strategy.permitsNonresponseAt history wait.occurrence

/-- `Compatible` consults permission only in the permanent-wait constructor. -/
def Compatible (strategy : model.EnvironmentStrategy) {history : model.History} :
    model.MaximalContinuation history → Prop
  | .terminal _ _ => True
  | .infinite _ => True
  | .waiting path wait => permitsNonresponse model strategy (history.append path) wait

/-- Exact generated maximal continuations from a selected history. -/
def Generated (strategy : model.EnvironmentStrategy) (history : model.History) :=
  {continuation : model.MaximalContinuation history // Compatible model strategy continuation}

end EnvironmentStrategy

/-- Settlement means that an actual allowed reply for this occurrence appears
in the retained finite path or infinite choice stream. -/
def Settles {history : model.History} (occurrence : model.boundary.Occurrence)
    (_pending : model.boundary.Pending history occurrence) :
    model.MaximalContinuation history → Prop
  | .terminal path _ | .waiting path _ =>
      ∃ response choice,
        model.protocol.Allowed (model.boundary.request occurrence) response ∧
        model.boundary.Reply occurrence response choice ∧ choice ∈ path.choices
  | .infinite continuation =>
      ∃ index response,
        model.protocol.Allowed (model.boundary.request occurrence) response ∧
        model.boundary.Reply occurrence response (continuation.choiceAt index)

/-- Fixed standard responsiveness: every generated maximal continuation from
every reached pending occurrence settles that exact occurrence. -/
def EnvironmentResponsive (strategy : model.EnvironmentStrategy) : Prop :=
  ∀ history occurrence (_pending : model.boundary.Pending history occurrence)
    (generated : EnvironmentStrategy.Generated model strategy history),
    model.Settles occurrence _pending generated.1

/-- Maximal-continuation existence is an explicit model law. It is not inferred
for arbitrary relational systems. -/
def ContinuationAdequate : Prop :=
  ∀ history : model.History, Nonempty (model.MaximalContinuation history)

/-- The responding strategy needs a root and a terminal or infinite continuation
from each reached history. -/
structure RespondingContinuationAdequate : Prop where
  root : Nonempty model.History
  continuation : ∀ history : model.History,
    ∃ continuation : model.MaximalContinuation history,
      match continuation with
      | .terminal _ _ => True
      | .infinite _ => True
      | .waiting _ _ => False

/-- Infinite settlement is an explicit eventual-reply law. Pointwise external
agency alone supplies no fairness or eventual response. -/
def InfiniteEventuallyReplies : Prop :=
  ∀ (history : model.History) occurrence,
    model.boundary.Pending history occurrence →
    ∀ continuation : model.system.InfiniteContinuation history.state history.graph
      history.path.events,
      ∃ index response,
        model.protocol.Allowed (model.boundary.request occurrence) response ∧
        model.boundary.Reply occurrence response (continuation.choiceAt index)

/-- `StrategyAdequate` requires a root and generated continuation at every history. -/
structure StrategyAdequate (strategy : model.EnvironmentStrategy) : Prop where
  root : Nonempty model.History
  continuation : ∀ history : model.History,
    Nonempty (EnvironmentStrategy.Generated model strategy history)

/-- The standard responsive witness couples one exact strategy to its
nonvacuity proof and responsiveness theorem. -/
structure ResponsiveStrategyWitness where
  strategy : model.EnvironmentStrategy
  adequate : StrategyAdequate model strategy
  responsive : model.EnvironmentResponsive strategy

/-- Terminality of a generated maximal continuation. -/
def IsTerminal {history : model.History} : model.MaximalContinuation history → Prop
  | .terminal _ _ => True
  | .infinite _ => False
  | .waiting _ _ => False

/-- Model-level conditional termination demand. Existence and the universal
claim are separate conjuncts, preventing a favorable witness from proving the
property for other adequate responsive strategies. -/
def TerminatesUnderResponsive : Prop :=
  Nonempty model.ResponsiveStrategyWitness ∧
    ∀ (strategy : model.EnvironmentStrategy), StrategyAdequate model strategy →
      model.EnvironmentResponsive strategy → ∀ (history : model.History),
        ∀ generated : EnvironmentStrategy.Generated model strategy history,
          model.IsTerminal generated.1

/-- Every actual terminal suffix is generated under every strategy. -/
def terminalGenerated (strategy : model.EnvironmentStrategy) (history : model.History)
    {state graph} (path : model.system.Path history.state history.graph state graph)
    (finished : model.system.Terminal state graph) :
    EnvironmentStrategy.Generated model strategy history :=
  ⟨.terminal path finished, trivial⟩

/-- Every productive or divergent infinite transition sequence is generated
under every strategy. -/
def infiniteGenerated (strategy : model.EnvironmentStrategy) (history : model.History)
    (continuation : model.system.InfiniteContinuation history.state history.graph
      history.path.events) : EnvironmentStrategy.Generated model strategy history :=
  ⟨.infinite continuation, trivial⟩

/-- Every allowed dependent response and every concrete realization of it
extends the exact history; the strategy has no predicate capable of pruning it. -/
theorem allowedResponseHistory (_strategy : model.EnvironmentStrategy)
    (history : model.History) (occurrence : model.boundary.Occurrence)
    (pending : model.boundary.Pending history occurrence)
    (response : model.protocol.Response (model.boundary.request occurrence))
    (allowed : model.protocol.Allowed (model.boundary.request occurrence) response) :
    ∃ state graph, ∃ beforeReply : model.system.Path history.state history.graph state graph,
      (∀ choice ∈ beforeReply.choices, ∀ earlier,
        ¬ model.boundary.Reply occurrence earlier choice) ∧
      model.boundary.Pending (history.append beforeReply) occurrence ∧
      ∃ choice event next nextGraph,
        model.boundary.Reply occurrence response choice ∧
        model.system.Step graph state choice event next nextGraph :=
  model.boundary.reply_path history occurrence pending response allowed

/-- The first transition of an infinite continuation from a pending frontier
uses the selected external agency. It need not complete the reply. -/
theorem infinite_first_external {history : model.History}
    (occurrence : model.boundary.Occurrence)
    (pending : model.boundary.Pending history occurrence)
    (continuation : model.system.InfiniteContinuation history.state history.graph
      history.path.events) :
    model.boundary.External occurrence (continuation.choiceAt 0) := by
  have step := continuation.step 0
  rw [continuation.graphZero, continuation.stateZero] at step
  exact model.boundary.step_external history occurrence pending _ _ _ _ step

private theorem Path.first_of_positive {Event : Type uSystem}
    {system : RelationalSystem Event}
    {start finish : system.State} {startGraph finishGraph : system.Graph}
    (path : system.Path start startGraph finish finishGraph) (positive : 0 < path.length) :
    ∃ choice event next nextGraph,
      ∃ first : system.Step startGraph start choice event next nextGraph,
        ∃ rest : system.Path next nextGraph finish finishGraph,
          path = (RelationalSystem.Path.snoc RelationalSystem.Path.nil choice event
            next nextGraph first).append rest := by
  induction path with
  | nil => simp [RelationalSystem.Path.length] at positive
  | @snoc state graph prior choice event next nextGraph transition ih =>
      cases prior with
      | nil => exact ⟨choice, event, next, nextGraph, transition, .nil, rfl⟩
      | @snoc priorState priorGraph earlier priorChoice priorEvent state graph priorStep =>
          have priorPositive : 0 <
              (RelationalSystem.Path.snoc earlier priorChoice priorEvent state graph priorStep).length := by
            simp [RelationalSystem.Path.length]
          obtain ⟨firstChoice, firstEvent, firstNext, firstGraph, firstStep, rest, equal⟩ :=
            ih priorPositive
          exact ⟨firstChoice, firstEvent, firstNext, firstGraph, firstStep,
            .snoc rest choice event next nextGraph transition, by rw [equal]; rfl⟩

/-- A positive finite path from a pending occurrence begins with a choice using
the selected external agency. That first choice need not complete the reply. -/
theorem finite_first_external {history : model.History}
    (occurrence : model.boundary.Occurrence)
    (pending : model.boundary.Pending history occurrence)
    {state graph} (path : model.system.Path history.state history.graph state graph)
    (positive : 0 < path.length) :
    ∃ choice event next nextGraph,
      model.boundary.External occurrence choice ∧
      model.system.Step history.graph history.state choice event next nextGraph := by
  obtain ⟨choice, event, next, nextGraph, first, rest, equal⟩ :=
    Path.first_of_positive path positive
  exact ⟨choice, event, next, nextGraph,
    model.boundary.step_external history occurrence pending choice event next nextGraph first,
    first⟩

@[simp] theorem history_append_nil (history : model.History) :
    history.append (.nil) = history := by
  cases history
  rfl

/-- Fixed responsiveness excludes permanent nonresponse at every exact reached
history, obtained by considering its zero-suffix waiting continuation. -/
theorem responsive_no_wait (strategy : model.EnvironmentStrategy)
    (responsive : EnvironmentResponsive model strategy) :
    ∀ history wait, ¬ EnvironmentStrategy.permitsNonresponse model strategy history wait := by
  intro history wait permitted
  cases history with
  | mk initialState initialGraph state graph validInitial path =>
      let history : model.History :=
        ⟨initialState, initialGraph, state, graph, validInitial, path⟩
      let empty : model.system.Path state graph state graph := .nil
      have same : history.append empty = history := by rfl
      let laterWait : RelationalSystem.PermanentWait model.boundary (history.append empty) :=
        same.symm ▸ wait
      have compatible : EnvironmentStrategy.permitsNonresponse model strategy
          (history.append empty) laterWait := by
        simpa [EnvironmentStrategy.permitsNonresponse, same] using permitted
      let generated : EnvironmentStrategy.Generated model strategy history :=
        ⟨.waiting empty laterWait, compatible⟩
      have settled := responsive history laterWait.occurrence laterWait.pending generated
      obtain ⟨response, choice, allowed, reply, member⟩ := settled
      simp [empty, RelationalSystem.Path.choices] at member

/-- If the model independently rules out infinite transition sequences, fixed
responsiveness makes every generated maximal continuation terminal. -/
theorem generated_terminal_of_responsive_no_infinite
    (strategy : model.EnvironmentStrategy)
    (responsive : EnvironmentResponsive model strategy)
    (noInfinite : ∀ (history : model.History),
      model.system.InfiniteContinuation history.state history.graph history.path.events → False)
    (history : model.History) (generated : EnvironmentStrategy.Generated model strategy history) :
    model.IsTerminal generated.1 := by
  rcases generated with ⟨continuation, compatible⟩
  cases continuation with
  | terminal path finished => trivial
  | infinite continuation => exact False.elim (noInfinite history continuation)
  | waiting path wait =>
      exact False.elim
        (model.responsive_no_wait strategy responsive (history.append path) wait compatible)

/-- The responding strategy is responsive when infinite continuations are
independently known eventually to contain an actual reply. -/
theorem responding_responsive (eventual : model.InfiniteEventuallyReplies) :
    EnvironmentResponsive model (EnvironmentStrategy.responding model) := by
  intro history occurrence pending generated
  rcases generated with ⟨continuation, compatible⟩
  cases continuation with
  | terminal path finished =>
      exact model.boundary.terminal_has_reply history occurrence pending path finished
  | infinite continuation => exact eventual history occurrence pending continuation
  | waiting path wait =>
      exact False.elim compatible

/-- A model with a maximal continuation from every history has an adequate
responding strategy, without selecting one favorable result branch. -/
theorem responding_adequate (adequate : model.RespondingContinuationAdequate) :
    StrategyAdequate model (EnvironmentStrategy.responding model) := by
  constructor
  · exact adequate.root
  intro history
  obtain ⟨continuation, usable⟩ := adequate.continuation history
  cases continuation with
  | terminal path finished => exact ⟨model.terminalGenerated _ history path finished⟩
  | infinite continuation => exact ⟨model.infiniteGenerated _ history continuation⟩
  | waiting path wait => exact False.elim usable

/-- Package the exact responding strategy with the same adequacy proof used to
show its generated tree is nonempty at every history. -/
def respondingWitness (adequate : model.RespondingContinuationAdequate)
    (eventual : model.InfiniteEventuallyReplies) :
    model.ResponsiveStrategyWitness where
  strategy := EnvironmentStrategy.responding model
  adequate := model.responding_adequate adequate
  responsive := model.responding_responsive eventual

end BehaviorModel
end Grass
