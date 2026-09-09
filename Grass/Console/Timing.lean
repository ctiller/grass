import Grass.Semantics.BoundaryTiming
import Grass.Console.Accounting

/-! Isolated boundary timing and conditional termination for console output. -/

namespace Grass.Console.Timing

open Grass.Std.Logical Grass.Semantics Grass.RelationalSystem
open Grass.Console.Behavior Grass.Console.Accounting

private def Good {payload : Vec Byte} : State payload → Prop
  | .pending _ => True
  | .finished cut cause => FinishAllowed cut cause

private theorem step_good {payload : Vec Byte} {before after : State payload}
    {choice : Choice payload} {event : Event} {beforeGraph afterGraph : Unit}
    (transition : (system payload).Step beforeGraph before choice event after afterGraph) : Good after := by
  cases beforeGraph
  cases afterGraph
  rcases choice with ⟨cut, response⟩
  cases response with
  | advance next strict =>
      rcases step_iff.mp transition with ⟨_, _, nextEq⟩
      subst after
      trivial
  | finish cause =>
      rcases step_iff.mp transition with ⟨_, allowed, _, nextEq⟩
      subst after
      exact allowed

private theorem steps_preserve
    {E : Type} {s : RelationalSystem E} {P : s.State → Prop}
    (every : ∀ {before choice event next beforeGraph nextGraph},
      s.Step beforeGraph before choice event next nextGraph → P next)
    {start finish : s.State} {startGraph finishGraph : s.Graph} {events : List E}
    (steps : s.Steps start startGraph events finish finishGraph) (initial : P start) : P finish := by
  induction steps with
  | refl => exact initial
  | step prior transition _ => exact every transition

private theorem history_state_valid {payload : Vec Byte}
    (history : (system payload).History) :
    Good history.state := by
  apply steps_preserve (s := system payload) (P := Good)
    (fun transition => step_good transition) history.path.steps
  rw [history.validInitial]
  trivial

/-- Every reachable console history has a maximal terminal extension. -/
theorem completionAdequate (payload : Vec Byte) :
    BoundaryTerminalAdequate (boundary payload) where
  complete := by
    intro history
    cases stateEq : history.state with
    | pending cut =>
      let choice : Choice payload := .reply cut (.finish .writeFailed)
      let event : Event := .terminal .writeFailed
      let next : State payload := .finished cut .writeFailed
      have step : (system payload).Step history.graph history.state choice event next () := by
        exact ⟨stateEq, trivial, rfl, rfl⟩
      let empty : (system payload).Path history.state history.graph
          history.state history.graph := .nil
      exact ⟨⟨next, (), .snoc empty choice event next () step,
        ⟨cut, .writeFailed, rfl, trivial⟩⟩⟩
    | finished cut cause =>
      have allowed : FinishAllowed cut cause := by
        have valid := history_state_valid history
        rw [stateEq] at valid
        exact valid
      exact ⟨⟨history.state, history.graph, .nil, ⟨cut, cause, stateEq, allowed⟩⟩⟩

/-- The console responding strategy satisfies the fixed boundary predicate. -/
theorem respondingResponsive (payload : Vec Byte) :
    BoundaryResponsive (BoundaryTimingStrategy.responding (boundary payload)) := by simp

/-- Every generated maximal console behavior terminates. Responsiveness rules
out only permanent nonresponse; the independent decreasing rank rules out an
infinite transition sequence. -/
theorem generated_terminates {payload : Vec Byte}
    (strategy : BoundaryTimingStrategy (boundary payload))
    (responsive : BoundaryResponsive strategy)
    (complete : strategy.GeneratedComplete) :
    ∃ history finished, complete.1 = CompleteHistory.terminal history finished := by
  rcases complete with ⟨complete, compatible⟩
  cases complete with
  | terminal history finished => exact ⟨history, finished, rfl⟩
  | infinite history continuation => exact False.elim (no_infinite_continuation continuation)
  | waiting history wait => exact False.elim (responsive history wait compatible)

/-- The responding generated domain is inhabited from every reachable history. -/
theorem respondingGeneratedNonempty {payload : Vec Byte}
    (history : (system payload).History) :
    Nonempty (BoundaryTimingStrategy.GeneratedComplete
      (BoundaryTimingStrategy.responding (boundary payload))) := by
  obtain ⟨complete⟩ := (completionAdequate payload).complete history
  exact ⟨BoundaryTimingStrategy.terminalCompatible _
    (history.append complete.path) complete.finished⟩

end Grass.Console.Timing
