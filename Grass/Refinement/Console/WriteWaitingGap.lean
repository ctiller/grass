import Grass.Refinement.Console.WriteWaiting
import Grass.Console.Behavior

/-! A concrete obstruction to complete-history coverage by the current byte
driver. Its published output at any held occurrence is a proper prefix of a
nonempty payload. The logical console permits waiting after the full payload.
This is a mismatch witness, not a narrowed refinement certificate.
-/

namespace Grass.Refinement.Console.WriteWaitingGap

open Grass.Process Grass.Std.Logical Grass.Std.Console Grass.Std.Console.WriteProcess
open Grass.RelationalSystem

theorem held_output_proper {payload : Vec Byte} (nonempty : 0 < payload.length)
    (point : (machine payload).Point) (occurrence : (machine payload).Occurrence)
    (held : (machine payload).held point = {occurrence}) :
    (emittedPrefix point.state).length < payload.length := by
  have present : occurrence ∈ (machine payload).held point := by rw [held]; simp
  have decision := (machine payload).held_issues present
  have located := (machine payload).held_point present
  change WriteProcess.decide occurrence.point.state = .effect occurrence.demand occurrence.resume at decision
  rw [located] at decision
  cases stateEq : point.state with
  | acquire => simpa [emittedPrefix] using nonempty
  | writing cursor =>
    rw [stateEq] at decision
    simp only [WriteProcess.decide] at decision
    split at decision
    · next more => simpa [emittedPrefix, Vec.length_take, Nat.min_eq_left cursor.within] using more
    · contradiction
  | publish cursor more response => simp [stateEq, WriteProcess.decide] at decision
  | finished outcome cursor => simp [stateEq, WriteProcess.decide] at decision
  | unavailable => simp [stateEq, WriteProcess.decide] at decision

/-- No exact-output matching lower permanent wait exists at the full cut. -/
theorem no_full_output_wait {payload : Vec Byte} (nonempty : 0 < payload.length)
    {mayWait : Demand payload → Prop} (history : (WriteHistory.system payload).History)
    (waiting : PermanentWait (WriteWaiting.boundary mayWait) history) :
    WriteHistory.historyBytes history.path.events ≠ payload := by
  intro equal
  have proper := held_output_proper nonempty history.state waiting.occurrence waiting.pending
  have accounting := (WriteHistory.runs_accounting history.erase.runs).2
  have same : emittedPrefix history.state.state = payload := accounting.symm.trans equal
  rw [same] at proper
  exact Nat.lt_irrefl _ proper

/-- `full_output_wait` constructs the upper behavior excluded by `no_full_output_wait`
for a nonempty payload. -/
def full_output_wait (payload : Vec Byte) :
    PermanentWait (Grass.Console.Behavior.boundary payload)
      (Grass.Console.Behavior.pendingAt payload (Grass.Semantics.OutputCut.full payload)) :=
  Grass.Console.Behavior.permanentWaitAt _ _

end Grass.Refinement.Console.WriteWaitingGap
