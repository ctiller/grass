import Grass.Platform.Win32.RawServicePreservation
import Tests.Platform.Win32RawServiceContinuation

namespace Grass.Tests.Win32RawServicePreservation

open Grass.Core Grass.Op Grass.Std.Logical
open Grass.Platform.Win32 Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader
open Grass.Platform.Win32.Raw
open Grass.Tests.Win32WriteFileService Grass.Tests.Win32RawStep
open Grass.Tests.Win32RawServiceContinuation

/-- Only the two actual fixture edges are used; the tail is unconstrained by
the bounded theorem and is not asserted to be an execution. -/
def rawAt : Nat → RawState
  | 0 => before
  | 1 => receipt₁.after
  | _ => receipt₂.after

theorem two_steps {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (n : Nat) (bounded : n < 2) :
    RawStep loaded Grass.Tests.Win32WriteFile.noEffects Grass.Tests.Win32WriteFileConsolePublication.environment noReturnInterpretation [] (rawAt n)
      (.providerService call record.agent action) quietEvent (rawAt (n + 1)) [] := by
  cases n with
  | zero => exact quiet_service loaded
  | succ n =>
      have zero : n = 0 := by omega
      subst n
      exact quiet_service₂ loaded

/-- Two actual service edges preserve the original frame and full pending
record at the finite endpoint; no continuation past that endpoint is supplied. -/
theorem two_edge_frame {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    receipt₂.after.metadata.pending.lookup call = some (WriteFile.embedPending record) ∧
      ∃ current, receipt₂.after.calls.lookup call = some (.writeFile current) ∧
        current.toReturnFrame = runtime.toReturnFrame ∧
        current.fifthSlot = runtime.fifthSlot ∧ current.loanPlan = runtime.loanPlan := by
  have preserved := RawStep.service_prefix_runtime rawAt (fun _ => [])
    (fun _ => record.agent) (fun _ => action) (fun _ => quietEvent) 2 (two_steps loaded)
    runtime (by rfl) record (by rfl) 2 (Nat.le_refl 2)
  exact preserved.2

/-- A recovered endpoint frame cannot replace the original continuation value. -/
theorem changed_continuation_rejected (current : WriteFileRuntime)
    (frame : current.toReturnFrame = runtime.toReturnFrame) :
    current.continuation ≠ 1 := by
  have same := congrArg ReturnFrame.continuation frame
  change current.continuation = (0 : BitVec 64) at same
  rw [same]
  decide

/-- The zero-edge case needs no service step, including no fictitious edge
after a possible immediate return. -/
theorem zero_edges {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    ∃ current, before.calls.lookup call = some (.writeFile current) ∧
      current.toReturnFrame = runtime.toReturnFrame ∧
      current.fifthSlot = runtime.fifthSlot ∧ current.loanPlan = runtime.loanPlan := by
  have preserved := RawStep.service_prefix_runtime (loaded := loaded) (call := call)
    (realization := Grass.Tests.Win32WriteFile.noEffects)
    (environment := Grass.Tests.Win32WriteFileConsolePublication.environment)
    (interpretation := noReturnInterpretation)
    rawAt (fun _ => []) (fun _ => record.agent) (fun _ => action) (fun _ => quietEvent)
    0 (fun n impossible => False.elim (Nat.not_lt_zero n impossible))
    runtime (by rfl) record (by rfl) 0 (Nat.le_refl 0)
  exact preserved.2.2

end Grass.Tests.Win32RawServicePreservation
