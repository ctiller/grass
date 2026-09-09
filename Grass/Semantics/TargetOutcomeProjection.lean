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

/-- The generic zero-on-success, one-on-failure convention for any status type
that provides those two numeric literals. -/
def successZeroFailureOneAs [DecidableEq Outcome] [OfNat Status 0]
    [OfNat Status 1] (success : Outcome) :
    TargetOutcomeProjection Outcome Status :=
  successOrFailure success 0 1

/-- The UInt32 form of the zero-on-success, one-on-failure convention.

This wrapper preserves the result inferred for existing unannotated calls;
targets with another status type use `successZeroFailureOneAs`. -/
def successZeroFailureOne [DecidableEq Outcome] (success : Outcome) :
    TargetOutcomeProjection Outcome UInt32 :=
  successZeroFailureOneAs success

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
  simp [successZeroFailureOne, successZeroFailureOneAs]

@[simp] theorem successZeroFailureOne_status_failure [DecidableEq Outcome]
    (success outcome : Outcome) (notSuccess : outcome ≠ success) :
    (successZeroFailureOne success).status outcome = 1 := by
  simp [successZeroFailureOne, successZeroFailureOneAs, notSuccess]

@[simp] theorem successZeroFailureOneAs_status_success [DecidableEq Outcome]
    [OfNat Status 0] [OfNat Status 1]
    (success : Outcome) :
    (successZeroFailureOneAs (Status := Status) success).status success = 0 := by
  simp [successZeroFailureOneAs]

@[simp] theorem successZeroFailureOneAs_status_failure [DecidableEq Outcome]
    [OfNat Status 0] [OfNat Status 1]
    (success outcome : Outcome) (notSuccess : outcome ≠ success) :
    (successZeroFailureOneAs (Status := Status) success).status outcome = 1 := by
  simp [successZeroFailureOneAs, notSuccess]

end TargetOutcomeProjection

end Grass
