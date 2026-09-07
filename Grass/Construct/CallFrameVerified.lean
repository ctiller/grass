import Grass.Construct.FrameCompose

/-!
# Verified call-frame sessions

`CallFrameTransition` records the only permitted lifecycle steps, including
exact receipts for acquired or released call loans and restored registers.
`CallFrameRun` composes those steps, and `CallFrameSession` requires a complete
prepared-to-closed run. `withCallFrame` consumes that lifecycle evidence before
delegating to verified frame composition; instruction correctness still comes
only from `FrameVerifiedBackend`.
-/

namespace Grass.Construct

open Grass.Core Grass.CFG Grass.Construct.Layout Grass.Construct.Fragment

universe u v w

/-- One checked call-frame use at an exact lifecycle phase. -/
structure CheckedCallFrameUse {profile : LayoutProfile}
    (frame : CheckedWin64Frame profile) (phase : CallFramePhase) where
  use : CallFrameUse profile
  frameExact : use.call.frame = frame.plan
  phaseExact : use.phase = phase
  valid : use.WellFormed

/-- One permitted transition between checked uses of the same call frame. -/
inductive CallFrameTransition {profile : LayoutProfile}
    (frame : CheckedWin64Frame profile) :
    {fromPhase toPhase : CallFramePhase} →
      CheckedCallFrameUse frame fromPhase →
      CheckedCallFrameUse frame toPhase → Type where
  /-- Acquire exactly the named nonempty, duplicate-free loan set. -/
  | acquire
      (source : CheckedCallFrameUse frame .prepared)
      (target : CheckedCallFrameUse frame .loaned)
      (acquired : List Name)
      (acquiredExact : target.use.liveCallLoans = acquired) :
      CallFrameTransition frame source target
  /-- Return from a call after releasing every live loan. -/
  | completeReturn
      (source : CheckedCallFrameUse frame .loaned)
      (target : CheckedCallFrameUse frame .returned)
      (released : List Name)
      (releasedExact : source.use.liveCallLoans = released) :
      CallFrameTransition frame source target
  /-- Enter unwinding after releasing every live loan. -/
  | unwind
      (source : CheckedCallFrameUse frame .loaned)
      (target : CheckedCallFrameUse frame .unwinding)
      (released : List Name)
      (releasedExact : source.use.liveCallLoans = released) :
      CallFrameTransition frame source target
  /-- Close a returned frame after restoring exactly its saved registers. -/
  | closeReturn
      (source : CheckedCallFrameUse frame .returned)
      (target : CheckedCallFrameUse frame .closed)
      (restored : List Grass.ISA.X86.Gpr)
      (restoredExact : restored = frame.plan.saved) :
      CallFrameTransition frame source target
  /-- Close an unwinding frame after restoring exactly its saved registers. -/
  | closeUnwind
      (source : CheckedCallFrameUse frame .unwinding)
      (target : CheckedCallFrameUse frame .closed)
      (restored : List Grass.ISA.X86.Gpr)
      (restoredExact : restored = frame.plan.saved) :
      CallFrameTransition frame source target

/-- A compositional path of permitted transitions between checked uses. -/
inductive CallFrameRun {profile : LayoutProfile}
    (frame : CheckedWin64Frame profile) :
    {fromPhase toPhase : CallFramePhase} →
      CheckedCallFrameUse frame fromPhase →
      CheckedCallFrameUse frame toPhase → Type where
  /-- The empty run leaves a checked use unchanged. -/
  | done {phase : CallFramePhase}
      (state : CheckedCallFrameUse frame phase) : CallFrameRun frame state state
  /-- Prefix one permitted transition to a remaining run. -/
  | next {fromPhase middlePhase toPhase : CallFramePhase}
      {source : CheckedCallFrameUse frame fromPhase}
      {middle : CheckedCallFrameUse frame middlePhase}
      {target : CheckedCallFrameUse frame toPhase}
      (step : CallFrameTransition frame source middle)
      (rest : CallFrameRun frame middle target) :
      CallFrameRun frame source target

/-- Prepared-to-closed lifecycle evidence for one checked call frame. -/
structure CallFrameSession {profile : LayoutProfile}
    (frame : CheckedWin64Frame profile) where
  prepared : CheckedCallFrameUse frame .prepared
  closed : CheckedCallFrameUse frame .closed
  run : CallFrameRun frame prepared closed

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
