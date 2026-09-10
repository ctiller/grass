import Grass.Refinement.Console.WriteFileHistory
import Grass.Platform.Win32.WriteFileConsolePublication
import Grass.Platform.Win32.WriteFileReturn

/-! Route-checked extension of the existing reached console history.

The check attributes this one new service publication to a fixed environment's
stdout route. It does not retrospectively attribute the earlier history, close
the selected handoff/physical realization obligations, or infer causal order
from the separate memory-event and boundary logs. Native applicability remains
owed. No second history representation is introduced.
-/

namespace Grass.Refinement.Console.WriteFileHistory.Aligned

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Op
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.ExecutionState

variable {R Outcome Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : CapturedSpecification resources Outcome}
  {projection : CapturedTargetProjection spec Status}
  {realization : Realization} {before : RawState} {initial : ProtocolState}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
  {action : Action} {output : Vec Byte}

/-- `extendConsole?` checks the new observation and appends the actual committed
step to the supplied reached history using `Aligned.extend`. Refusal is absence
of stdout attribution, not a WriteFile result or a memory-access failure. -/
def extendConsole? (receipt : ServiceReceipt realization before call record action output)
    {relation : HandoffRelation (plan := receipt.runtime.loanPlan) projection}
    {history : History receipt.runtime.loanPlan realization initial call record receipt.pre}
    (aligned : Aligned relation history) (environment : ConsoleEnvironment)
    (observation : ConsolePublication.Observation) :
    Option (Aligned relation (.step history action output receipt.committed)) :=
  if ConsolePublication.matches? environment receipt observation then
    if ConsolePublication.onStdout environment observation then
      some (aligned.extend action output receipt.committed)
    else none
  else none

variable {receipt : ServiceReceipt realization before call record action output}
  {relation : HandoffRelation (plan := receipt.runtime.loanPlan) projection}
  {history : History receipt.runtime.loanPlan realization initial call record receipt.pre}
  {aligned : Aligned relation history} {environment : ConsoleEnvironment}
  {observation : ConsolePublication.Observation}
  {extended : Aligned relation (.step history action output receipt.committed)}

theorem extendConsole?_accepted
    (accepted : extendConsole? receipt aligned environment observation = some extended) :
    ConsolePublication.matches? environment receipt observation = true ∧
      ConsolePublication.onStdout environment observation = true ∧
      extended = aligned.extend action output receipt.committed := by
  unfold extendConsole? at accepted
  split at accepted <;> simp_all

/-- The admitted extension uses the exact generational binding on the selected
stdout route; the snapshot's relation to native handles is still external. -/
theorem extendConsole?_target
    (accepted : extendConsole? receipt aligned environment observation = some extended) :
    ∃ binding, environment.routeOf? record.request.handle = some binding ∧
      binding.generation = observation.handle.generation ∧
      binding.route = environment.stdoutRoute ∧ binding.writable = true ∧
      binding.mode = .synchronous := by
  have checked := extendConsole?_accepted accepted
  obtain ⟨_, _, _, _, _, binding, lookup, generation, route, writable, mode⟩ :=
    ConsolePublication.matched_target checked.1
  exact ⟨binding, lookup, generation,
    route.trans ((ConsolePublication.onStdout_eq_true_iff _ _).mp checked.2.1), writable, mode⟩

theorem extendConsole?_start
    (accepted : extendConsole? receipt aligned environment observation = some extended) :
    extended.start = aligned.start := by
  rw [(extendConsole?_accepted accepted).2.2]
  exact aligned.extend_start action output receipt.committed

theorem extendConsole?_endpoint
    (accepted : extendConsole? receipt aligned environment observation = some extended) :
    extended.endpoint = WriteFileProjection.cut aligned.start.cut aligned.start.suffix receipt.post := by
  rw [(extendConsole?_accepted accepted).2.2]
  rfl

/-- Positive output extends the same upper history, including its graph and
earlier choices, by the existing literal publication path. -/
theorem extendConsole?_positive
    (accepted : extendConsole? receipt aligned environment observation = some extended)
    (positive : receipt.pre.accepted < receipt.post.accepted) :
    extended.upper = aligned.upper.append
      (aligned.publicationPath action output receipt.committed positive) := by
  rw [(extendConsole?_accepted accepted).2.2]
  exact aligned.extend_positive action output receipt.committed positive

theorem extendConsole?_positive_events
    (accepted : extendConsole? receipt aligned environment observation = some extended)
    (positive : receipt.pre.accepted < receipt.post.accepted) :
    extended.upper.path.events = aligned.upper.path.events ++ [.emitted observation.bytes] := by
  have checked := extendConsole?_accepted accepted
  rw [checked.2.2, aligned.extend_positive_events action output receipt.committed positive,
    ConsolePublication.matched_bytes checked.1]

/-- Zero publication retains the entire upper history; it emits no new event. -/
theorem extendConsole?_zero
    (accepted : extendConsole? receipt aligned environment observation = some extended)
    (same : receipt.post.accepted = receipt.pre.accepted) :
    extended.upper = aligned.upper := by
  rw [(extendConsole?_accepted accepted).2.2]
  exact aligned.extend_zero action output receipt.committed same

/-- A matched FALSE return at this exact reached endpoint exposes no trusted
count and retains the already projected publication. Its physical return
interpretation remains an explicit premise of `MatchedReturn`. -/
theorem extendConsole?_failed_return
    (accepted : extendConsole? receipt aligned environment observation = some extended)
    {selected : ReturnInterpretation} {result : ReturnResult} {after : ProtocolState}
    (returned : MatchedReturn selected (.step history action output receipt.committed) result after)
    (failed : result.rawBool = 0) :
    result.reportedCount = none ∧
      Behavior.emittedBytes extended.upper.path.events =
        Behavior.emittedBytes aligned.start.upper.path.events ++
          (history.published ++ observation.bytes) := by
  refine ⟨returned.conforms.failure failed, ?_⟩
  rw [extended.output_exact, extendConsole?_start accepted,
    ConsolePublication.matched_bytes (extendConsole?_accepted accepted).1]
  rfl

end Grass.Refinement.Console.WriteFileHistory.Aligned
