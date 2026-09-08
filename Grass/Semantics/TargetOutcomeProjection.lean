/-!
# Target outcome projection

Target outcome policy is explicit program data.  It translates a portable
outcome to the terminal status selected by a concrete target without making
that target convention part of the portable specification.
-/

namespace Grass

universe u v

/-- A reviewed target-level translation from portable outcomes to terminal
statuses. -/
structure TargetOutcomeProjection (Outcome : Type u) (Status : Type v) where
  status : Outcome -> Status

namespace TargetOutcomeProjection

variable {Outcome : Type u} {Status : Type v}

/-- Select one portable success outcome and map every other admitted outcome
to the chosen failure status. -/
def successOrFailure [DecidableEq Outcome] (success : Outcome)
    (successCode failureCode : Status) :
    TargetOutcomeProjection Outcome Status where
  status outcome := if outcome = success then successCode else failureCode

/-- The named target convention whose selected success status is zero and
whose status for every other portable outcome is one. -/
def successZeroFailureOne [DecidableEq Outcome] (success : Outcome) :
    TargetOutcomeProjection Outcome UInt32 :=
  successOrFailure success 0 1

@[simp] theorem successOrFailure_status_success [DecidableEq Outcome]
    (success : Outcome) (successCode failureCode : Status) :
    (successOrFailure success successCode failureCode).status success =
      successCode := by
  simp [successOrFailure]

@[simp] theorem successOrFailure_status_failure [DecidableEq Outcome]
    (success outcome : Outcome) (successCode failureCode : Status)
    (notSuccess : outcome ≠ success) :
    (successOrFailure success successCode failureCode).status outcome =
      failureCode := by
  simp [successOrFailure, notSuccess]

@[simp] theorem successZeroFailureOne_status_success [DecidableEq Outcome]
    (success : Outcome) :
    (successZeroFailureOne success).status success = 0 := by
  simp [successZeroFailureOne]

@[simp] theorem successZeroFailureOne_status_failure [DecidableEq Outcome]
    (success outcome : Outcome) (notSuccess : outcome ≠ success) :
    (successZeroFailureOne success).status outcome = 1 := by
  simp [successZeroFailureOne, notSuccess]

end TargetOutcomeProjection

end Grass
