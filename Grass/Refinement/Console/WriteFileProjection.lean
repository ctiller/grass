import Grass.Platform.Win32.WriteFile
import Grass.Console.Behavior

variable {plan : Grass.Platform.Win32.WriteFile.LoanPlan}

/-! Project the existing occurrence-indexed WriteFile evidence into the exact
rendered console cut. The selected call writes the suffix at `start`; accepted
bytes are provider evidence, never inferred from an application-visible DWORD.
No return, wait adequacy, or infinite-stuttering theorem is asserted here.
-/

namespace Grass.Refinement.Console.WriteFileProjection

open Grass.Std.Logical Grass.Semantics Grass.Op
open Grass.Platform.Win32.WriteFile

variable {payload : Vec Byte} {state : ProtocolState}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}

/-- The same call and pending record determine the global output frontier. -/
def cut (start : OutputCut payload) (suffix : record.request.bytes = start.remaining)
    (frontier : Prefix plan state call record) : OutputCut payload where
  offset := start.offset + frontier.accepted
  bounded := by
    have bounded := frontier.bounded
    rw [suffix] at bounded
    simp only [OutputCut.remaining, Vec.length_drop] at bounded
    have within := start.bounded
    omega

theorem prefix_exact (start : OutputCut payload) (suffix : record.request.bytes = start.remaining)
    (frontier : Prefix plan state call record) :
    start.emitted ++ frontier.output = (cut start suffix frontier).emitted := by
  simp only [Prefix.output, suffix, OutputCut.remaining, OutputCut.emitted, cut]
  exact (Vec.take_add payload start.offset frontier.accepted).symm

/-- Reachability uses the actual handoff history, not a free-standing Prefix. -/
theorem history_prefix_exact {realization : Realization} {initial : ProtocolState}
    {frontier : Prefix plan state call record} (start : OutputCut payload)
    (suffix : record.request.bytes = start.remaining)
    (history : History plan realization initial call record frontier) :
    start.emitted ++ history.published = (cut start suffix frontier).emitted := by
  rw [history.published_eq_output]
  exact prefix_exact start suffix frontier

variable {before after : ProtocolState}
  {pre : Prefix plan before call record} {post : Prefix plan after call record}
  {realization : Realization} {action : Action} {output : Vec Byte}

/-- A provider publication is exactly the interval between projected cuts. -/
theorem publication_between (start : OutputCut payload)
    (suffix : record.request.bytes = start.remaining)
    (step : CommittedStep realization pre post action output) :
    output = (cut start suffix pre).between (cut start suffix post) := by
  rw [step.publication.suffix, suffix]
  simp only [OutputCut.remaining, OutputCut.between, cut, Vec.drop_drop]
  congr 1
  omega

/-- Positive publication takes a genuine upper step at the matching frontier. -/
theorem positive_step (start : OutputCut payload)
    (suffix : record.request.bytes = start.remaining)
    (step : CommittedStep realization pre post action output)
    (positive : pre.accepted < post.accepted) :
    (Grass.Console.Behavior.system payload).Step ()
      (.pending (cut start suffix pre))
      (.reply (cut start suffix pre) (.advance (cut start suffix post) (by
        change start.offset + pre.accepted < start.offset + post.accepted
        omega)))
      (.emitted output) (.pending (cut start suffix post)) () :=
  ⟨rfl, congrArg Grass.Console.Behavior.Event.emitted (publication_between start suffix step), rfl⟩

/-- Zero accepted advance changes neither the cut nor its output. This local
classification alone does not justify hiding an infinite provider execution. -/
theorem zero_step (start : OutputCut payload)
    (suffix : record.request.bytes = start.remaining)
    (step : CommittedStep realization pre post action output)
    (same : post.accepted = pre.accepted) :
    cut start suffix post = cut start suffix pre ∧ output = Vec.empty := by
  constructor
  · apply OutputCut.ext
    simp [cut, same]
  · rw [step.publication.suffix, same, Nat.sub_self, Vec.take_zero]

/-- Both frontiers hold the original call's identical pending record. -/
theorem same_occurrence (_step : CommittedStep realization pre post action output) :
    before.pending.lookup call = some (embedPending record) ∧
      after.pending.lookup call = some (embedPending record) :=
  ⟨pre.pending.lookup, post.pending.lookup⟩

end Grass.Refinement.Console.WriteFileProjection
