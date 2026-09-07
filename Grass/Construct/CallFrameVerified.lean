import Grass.Construct.FrameCompose

/-!
# Verified call-frame sessions

`CallFrameSession` binds one checked frame to explicit valid prepared and closed
`CallFrameUse` states. `withCallFrame` requires that lifecycle evidence before
delegating to verified frame composition; instruction correctness still comes
only from `FrameVerifiedBackend`.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Layout Grass.Construct.Fragment

universe u v w

/-- One checked call-frame use at an exact lifecycle phase. -/
structure CheckedCallFrameUse {profile : LayoutProfile}
    (frame : CheckedWin64Frame profile) (phase : CallFramePhase) where
  use : CallFrameUse profile
  frameExact : use.call.frame = frame.plan
  phaseExact : use.phase = phase
  valid : use.WellFormed

/-- Prepared-to-closed lifecycle evidence for one checked call frame. -/
structure CallFrameSession {profile : LayoutProfile}
    (frame : CheckedWin64Frame profile) where
  prepared : CheckedCallFrameUse frame .prepared
  closed : CheckedCallFrameUse frame .closed

namespace FrameVerifiedBackend

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State} {effectModel : EffectModel Instruction Effect}
  {profile : LayoutProfile}

/-- Compose a verified framed body only with explicit prepared/closed evidence. -/
def withCallFrame
    (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    (laws : SequentialLaws semantics effectModel)
    (frame : CheckedWin64Frame profile)
    (_session : CallFrameSession frame)
    {bodyContract : BlockContract State}
    (body : VerifiedFragment semantics effectModel bodyContract)
    (enterBoundary : BoundaryCompatible (backend.enterContract frame) bodyContract)
    (leaveBoundary : BoundaryCompatible
      (thenContract (backend.enterContract frame) bodyContract)
      (backend.leaveContract frame)) :=
  backend.withFrame laws frame body enterBoundary leaveBoundary

/-- `withCallFrame_expand` retains exact prologue/body/epilogue source order. -/
@[simp] theorem withCallFrame_expand
    (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    (laws : SequentialLaws semantics effectModel)
    (frame : CheckedWin64Frame profile)
    (session : CallFrameSession frame)
    {bodyContract : BlockContract State}
    (body : VerifiedFragment semantics effectModel bodyContract)
    (enterBoundary : BoundaryCompatible (backend.enterContract frame) bodyContract)
    (leaveBoundary : BoundaryCompatible
      (thenContract (backend.enterContract frame) bodyContract)
      (backend.leaveContract frame)) :
    (backend.withCallFrame laws frame session body enterBoundary leaveBoundary).source.expand =
      (backend.enter frame).source.expand ++ body.source.expand ++
        (backend.leave frame).source.expand := by
  simp [withCallFrame]

end FrameVerifiedBackend

end Grass.Construct
