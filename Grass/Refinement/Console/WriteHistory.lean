import Grass.Std.Console.Process
import Grass.Semantics.Execution

/-!
# Finite histories of the portable write consumer

This is an operational view of the existing sequential adapter, using the
shared `RelationalSystem.Runs` and `RelationalSystem.Steps` relations. The
adapter determines the issued bag; `step_iff` relates this view to its exact
step relation. No provider assumptions or alternative write policy are added.

The graph is `Unit`: this isolated sequential reference model has no extra
graph constraints. Infinite consistency imposes no additional global condition
on sequences of its steps. In particular, this view does not represent an
infinitely pending external operation as an infinite stream of fake steps.
It is not Hello's complete-history contract, a responsiveness theorem, or a
refinement of physical I/O. Byte histories here are the model's published
observations, including its ghost failure-emission witnesses.
-/

namespace Grass.Refinement.Console.WriteHistory

open Grass.Std.Logical Grass.Std.Console Grass.Std.Console.WriteProcess

/-- The exact adapter in the shared execution vocabulary. -/
def system (payload : Vec Byte) : RelationalSystem (List (Vec Byte)) where
  State := (machine payload).Point
  Choice := (machine payload).Event
  Graph := Unit
  Initial := fun point _ =>
    (program payload).Initial () point ((machine payload).held point) []
  Step := fun _ before choice observations after _ =>
    (program payload).Step before choice after ((machine payload).held after) observations
  Terminal := fun point _ => ∃ result, (program payload).terminal () point result
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := Eq
  extendsRefl := fun _ => rfl
  extendsTrans := Eq.trans
  stepExtends := fun _ => Subsingleton.elim _ _

/-- `step_iff` recovers exactly the issued bag forced by the adapter. -/
theorem step_iff {payload : Vec Byte} (before after : (machine payload).Point)
    (choice : (machine payload).Event) (observations : List (Vec Byte)) :
    (system payload).Step () before choice observations after () ↔
      ∃ issued, (program payload).Step before choice after issued observations := by
  constructor
  · intro step; exact ⟨_, step⟩
  · rintro ⟨issued, step⟩
    have issuedEq := step.2.1
    subst issued
    exact step

/-- Concatenate the observation segments of a finite history. -/
def historyBytes : List (List (Vec Byte)) → Vec Byte
  | [] => Vec.empty
  | observations :: rest => bytesOf observations ++ historyBytes rest

/-- `historyBytes_append` accounts for concatenated finite histories. -/
theorem historyBytes_append (left right : List (List (Vec Byte))) :
    historyBytes (left ++ right) = historyBytes left ++ historyBytes right := by
  induction left with
  | nil => simp [historyBytes]
  | cons observations rest ih => simp [historyBytes, ih, Vec.append_assoc]

/-- `steps_accounting` lifts the adapter equation over every coherent finite suffix. -/
theorem steps_accounting {payload : Vec Byte}
    {before after : (system payload).State} {beforeGraph afterGraph : Unit}
    {events : List (List (Vec Byte))}
    (steps : (system payload).Steps before beforeGraph events after afterGraph)
    (valid : Valid before.state) :
    Valid after.state ∧
      emittedPrefix after.state = emittedPrefix before.state ++ historyBytes events := by
  induction steps with
  | refl => exact ⟨valid, by simp [historyBytes]⟩
  | @step history current currentGraph choice observations next nextGraph
      prior transition ih =>
    obtain ⟨nextValid, accounting⟩ :=
      step_accounting current next choice _ observations ih.1 transition
    exact ⟨nextValid, by
      rw [accounting, ih.2]
      simp [historyBytes_append, historyBytes, Vec.append_assoc]⟩

/-- `runs_accounting` identifies all published bytes with the reached state's prefix. -/
theorem runs_accounting {payload : Vec Byte}
    {initial final : (system payload).State} {initialGraph finalGraph : Unit}
    {events : List (List (Vec Byte))}
    (run : (system payload).Runs initial initialGraph final finalGraph events) :
    Valid final.state ∧ historyBytes events = emittedPrefix final.state := by
  have initialEq : initial = ⟨0, State.acquire⟩ := run.initialValid.1
  have initialValid : Valid initial.state := by rw [initialEq]; trivial
  obtain ⟨valid, accounting⟩ := steps_accounting run.steps initialValid
  refine ⟨valid, ?_⟩
  simpa [initialEq, emittedPrefix] using accounting.symm

/-- Every finite run publishes a bounded prefix, including unfinished runs. -/
theorem run_prefix {payload : Vec Byte}
    (execution : (system payload).ExecutionPrefix) :
    ∃ count, count ≤ payload.length ∧ historyBytes execution.events = payload.take count := by
  rw [(runs_accounting execution.runs).2]
  exact state_prefix execution.state.state

/-- Successful completed runs publish the complete payload. -/
theorem run_success {payload : Vec Byte}
    (execution : (system payload).ExecutionPrefix) (cursor : WriteCursor payload)
    (terminal : (program payload).terminal () execution.state (.written .success cursor)) :
    historyBytes execution.events = payload := by
  obtain ⟨valid, accounting⟩ := runs_accounting execution.runs
  rw [accounting, terminal_prefix _ _ _ terminal,
    terminal_success _ _ valid terminal, Vec.take_length]

/-- No-progress completed runs publish a proper prefix. -/
theorem run_noProgress {payload : Vec Byte}
    (execution : (system payload).ExecutionPrefix) (cursor : WriteCursor payload)
    (terminal : (program payload).terminal () execution.state (.written .noProgress cursor)) :
    historyBytes execution.events = payload.take cursor.committed ∧
      cursor.committed < payload.length := by
  obtain ⟨valid, accounting⟩ := runs_accounting execution.runs
  exact ⟨accounting.trans (terminal_prefix _ _ _ terminal),
    terminal_noProgress _ _ valid terminal⟩

/-- Failure completed runs retain their entire witnessed prefix, possibly the payload. -/
theorem run_writeFailed {payload : Vec Byte}
    (execution : (system payload).ExecutionPrefix) (cursor : WriteCursor payload)
    (terminal : (program payload).terminal () execution.state (.written .writeFailed cursor)) :
    historyBytes execution.events = payload.take cursor.committed :=
  (runs_accounting execution.runs).2.trans (terminal_prefix _ _ _ terminal)

/-- Unavailable-output completed runs publish no bytes. -/
theorem run_unavailable {payload : Vec Byte}
    (execution : (system payload).ExecutionPrefix)
    (terminal : (program payload).terminal () execution.state .unavailable) :
    historyBytes execution.events = Vec.empty :=
  (runs_accounting execution.runs).2.trans (terminal_unavailable _ terminal)

end Grass.Refinement.Console.WriteHistory
