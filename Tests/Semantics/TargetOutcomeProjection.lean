import Grass.Semantics.TargetOutcomeProjection

namespace Grass.Tests.TargetOutcomeProjection

inductive Outcome
  | success
  | unavailable
  | failed
  deriving DecidableEq

def policy : TargetOutcomeProjection Outcome UInt32 :=
  .successZeroFailureOne .success

def inferredPolicy := TargetOutcomeProjection.successZeroFailureOne Outcome.success

def naturalPolicy : TargetOutcomeProjection Outcome Nat :=
  .successZeroFailureOneAs .success

example : TargetOutcomeProjection Outcome UInt32 := inferredPolicy

example : policy.status .success = 0 := by decide

example : policy.status .unavailable = 1 := by decide

example : policy.status .failed = 1 := by decide

example :
    (TargetOutcomeProjection.successZeroFailureOneAs (Status := Nat) Outcome.success).status
        .success = 0 := by
  simp

example :
    (TargetOutcomeProjection.successZeroFailureOneAs (Status := Nat) Outcome.success).status
        .failed = 1 := by
  simp

end Grass.Tests.TargetOutcomeProjection
