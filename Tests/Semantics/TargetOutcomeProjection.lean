import Grass.Semantics.TargetOutcomeProjection

namespace Grass.Tests.TargetOutcomeProjection

inductive Outcome
  | success
  | unavailable
  | failed
  deriving DecidableEq

def policy : TargetOutcomeProjection Outcome UInt32 :=
  .successZeroFailureOne .success

example : policy.status .success = 0 := by decide

example : policy.status .unavailable = 1 := by decide

example : policy.status .failed = 1 := by decide

end Grass.Tests.TargetOutcomeProjection
