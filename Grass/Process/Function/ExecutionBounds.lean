import Grass.Process.Function.Serial

/-! Numeric bounds on actual serial executions, including executions represented
by a process-level collapse. These count source internal steps; they neither
bound host time nor establish cancellation delivery or provider responsiveness. -/

namespace Grass.Process

universe u w

namespace SerialFunctionSource

variable {State : Type w} {contract : SerialFunctionContract State}
  {source : SerialFunctionSource contract}

/-- A bounded path forces every sequence following the same source's actual
decisions to reach that exact endpoint within the supplied budget. -/
theorem InternalStepsWithin.forces_endpoint_on_sequence
    {fuel : Nat} {start finish : source.Machine}
    (bounded : source.InternalStepsWithin fuel start finish)
    (run : Nat → source.Machine) (starts : run 0 = start)
    (advances : ∀ index next, source.decide (run index) = .internal next →
      run (index + 1) = next) :
    ∃ index ≤ fuel, run index = finish := by
  induction bounded generalizing run with
  | refl fuel state => exact ⟨0, Nat.zero_le fuel, starts⟩
  | @step fuel start middle finish first rest ih =>
    have firstRun : run (0 + 1) = middle := advances 0 middle (starts ▸ first)
    obtain ⟨index, within, reached⟩ := ih (fun index => run (index + 1)) firstRun
      (by
        intro index next step
        exact advances (index + 1) next step)
    exact ⟨index + 1, Nat.add_le_add_right within 1, reached⟩

end SerialFunctionSource

namespace SerialFunctionRealizes

variable {State : Type w} {contract : SerialFunctionContract State}
  {source : SerialFunctionSource contract}

/-- Every actual source execution at an admitted call reaches a declared
contract exit within its selected work bound, with its actual final state. -/
theorem actual_execution_bounded (realizes : SerialFunctionRealizes contract source)
    (bound : contract.Input → State → Nat) (selected : contract.workBound = some bound)
    (input : contract.Input) (before : State) (pre : contract.Pre input before)
    (run : Nat → source.Machine) (starts : run 0 = source.enter input before)
    (advances : ∀ index next, source.decide (run index) = .internal next →
      run (index + 1) = next) :
    ∃ index ≤ bound input before, ∃ exit,
      source.decide (run index) = .exit exit ∧
        contract.Post input exit before (source.read (run index)) := by
  obtain ⟨finish, bounded, exits⟩ := realizes.bounded bound selected input before pre
  obtain ⟨index, within, reached⟩ := bounded.forces_endpoint_on_sequence run starts advances
  cases decision : source.decide finish with
  | internal next => simp [decision, SerialDecision.IsExit] at exits
  | exit exit =>
    refine ⟨index, within, exit, ?_, ?_⟩
    · simpa [reached] using decision
    · rw [reached]
      exact realizes.exitsPost input before finish exit pre bounded.toSteps decision

end SerialFunctionRealizes

namespace CollapsesToOneTransition

variable {p : ProcessSpec.{u, w}} {contract : SerialFunctionContract p.State}
  {Exclusive : contract.Input → p.State → Prop} {LinearizationPoint : Type w}
  {LinearizesAt : LinearizationPoint → contract.Input → p.State → Prop}
  {Noninterference : LinearizationPoint → contract.Input → p.State → Prop}
  {event : ProcessEvent p.vocabulary}

/-- A collapsed serial call admits the endpoint of every actual bounded source
execution as its process step, preserving the exact state read by that source. -/
theorem actual_execution_bounded
    (collapse : CollapsesToOneTransition contract Exclusive LinearizationPoint
      LinearizesAt Noninterference event)
    (bound : contract.Input → p.State → Nat) (selected : contract.workBound = some bound)
    (input : contract.Input) (before : p.State) (pre : contract.Pre input before)
    (run : Nat → collapse.source.Machine)
    (starts : run 0 = collapse.source.enter input before)
    (advances : ∀ index next, collapse.source.decide (run index) = .internal next →
      run (index + 1) = next) :
    ∃ index ≤ bound input before, ∃ exit,
      collapse.source.decide (run index) = .exit exit ∧
        contract.Post input exit before (collapse.source.read (run index)) ∧
        p.Step before event (collapse.source.read (run index)) 0 [] := by
  obtain ⟨index, within, exit, decision, post⟩ :=
    collapse.realizes.actual_execution_bounded bound selected input before pre run starts advances
  exact ⟨index, within, exit, decision, post,
    collapse.sound input exit before (collapse.source.read (run index)) pre post⟩

end CollapsesToOneTransition
end Grass.Process
