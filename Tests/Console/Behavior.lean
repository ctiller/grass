import Grass.Console.Behavior

namespace Grass.Tests.Console.Behavior

open Grass.Std.Logical Grass.Semantics Grass.RelationalSystem
open Grass.Console.Behavior

/-- A failed write may follow an exact full output cut. -/
theorem writeFailed_at_full (payload : Vec Byte) :
    FinishAllowed (OutputCut.full payload) .writeFailed := trivial

/-- No-progress is unavailable after the entire fixed payload was emitted. -/
theorem noProgress_not_full (payload : Vec Byte) :
    ¬ FinishAllowed (OutputCut.full payload) .noProgress := by
  simp [FinishAllowed, OutputCut.full]

/-- Unavailable stdout cannot be reported after a positive emitted prefix. -/
theorem unavailable_not_after_positive (payload : Vec Byte) (cut : OutputCut payload)
    (positive : 0 < cut.offset) : ¬ FinishAllowed cut .stdoutUnavailable := by
  simp [FinishAllowed]
  omega

/-- A nonempty request has a distinct reachable pending frontier. -/
theorem pending_nonempty_cut (payload : Vec Byte) (nonempty : 0 < payload.length) :
    ∃ cut : OutputCut payload, 0 < cut.offset ∧
      (pendingAt payload cut).state = .pending cut := by
  refine ⟨OutputCut.full payload, by simpa [OutputCut.full] using nonempty,
    pendingAt_state payload (OutputCut.full payload)⟩

end Grass.Tests.Console.Behavior
