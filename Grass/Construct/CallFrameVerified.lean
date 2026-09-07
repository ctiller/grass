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

/-- Transparent action recorded by a checked call-frame transition. -/
inductive CallFrameAction where
  | acquire (loans : List Name)
  | releaseReturn (loans : List Name)
  | releaseUnwind (loans : List Name)
  | restoreReturn (registers : List Grass.ISA.X86.Gpr)
  | restoreUnwind (registers : List Grass.ISA.X86.Gpr)
deriving Repr, DecidableEq

namespace CallFrameTransition

/-- Reveal the exact resource action carried by one transition witness. -/
def action {profile : LayoutProfile} {frame : CheckedWin64Frame profile}
    {fromPhase toPhase : CallFramePhase}
    {source : CheckedCallFrameUse frame fromPhase}
    {target : CheckedCallFrameUse frame toPhase}
    (transition : CallFrameTransition frame source target) : CallFrameAction :=
  match transition with
  | .acquire _ _ acquired _ => .acquire acquired
  | .completeReturn _ _ released _ => .releaseReturn released
  | .unwind _ _ released _ => .releaseUnwind released
  | .closeReturn _ _ restored _ => .restoreReturn restored
  | .closeUnwind _ _ restored _ => .restoreUnwind restored

end CallFrameTransition

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

namespace CallFrameRun

/-- Concatenate compatible checked lifecycle runs. -/
def append {profile : LayoutProfile} {frame : CheckedWin64Frame profile}
    {startPhase middlePhase endPhase : CallFramePhase}
    {start : CheckedCallFrameUse frame startPhase}
    {middle : CheckedCallFrameUse frame middlePhase}
    {finish : CheckedCallFrameUse frame endPhase}
    (first : CallFrameRun frame start middle)
    (second : CallFrameRun frame middle finish) : CallFrameRun frame start finish :=
  match first with
  | .done _ => second
  | .next step rest => .next step (append rest second)

/-- Reveal every exact resource action in lifecycle order. -/
def actions {profile : LayoutProfile} {frame : CheckedWin64Frame profile}
    {startPhase endPhase : CallFramePhase}
    {start : CheckedCallFrameUse frame startPhase}
    {finish : CheckedCallFrameUse frame endPhase}
    (run : CallFrameRun frame start finish) : List CallFrameAction :=
  match run with
  | .done _ => []
  | .next step rest => step.action :: actions rest

/-- Concatenating runs concatenates their transparent action traces exactly. -/
@[simp] theorem actions_append {profile : LayoutProfile}
    {frame : CheckedWin64Frame profile}
    {startPhase middlePhase endPhase : CallFramePhase}
    {start : CheckedCallFrameUse frame startPhase}
    {middle : CheckedCallFrameUse frame middlePhase}
    {finish : CheckedCallFrameUse frame endPhase}
    (first : CallFrameRun frame start middle)
    (second : CallFrameRun frame middle finish) :
    actions (append first second) = actions first ++ actions second := by
  induction first with
  | done => rfl
  | next step rest ih => simp [append, actions, ih]

end CallFrameRun

/-- Prepared-to-closed lifecycle evidence for one checked call frame. -/
structure CallFrameSession {profile : LayoutProfile}
    (frame : CheckedWin64Frame profile) where
  prepared : CheckedCallFrameUse frame .prepared
  closed : CheckedCallFrameUse frame .closed
  run : CallFrameRun frame prepared closed

namespace CallFrameSession

/-- Reveal the exact resource actions witnessed by a complete session. -/
def actions {profile : LayoutProfile} {frame : CheckedWin64Frame profile}
    (session : CallFrameSession frame) : List CallFrameAction :=
  session.run.actions

/-- Every complete session has exactly the normal-return or unwind trace shape. -/
theorem actions_shape {profile : LayoutProfile} {frame : CheckedWin64Frame profile}
    (session : CallFrameSession frame) :
    ∃ loans : List Name,
      session.actions =
        [.acquire loans, .releaseReturn loans, .restoreReturn frame.plan.saved] ∨
      session.actions =
        [.acquire loans, .releaseUnwind loans, .restoreUnwind frame.plan.saved] := by
  rcases session with ⟨prepared, closed, run⟩
  cases run with
  | next acquire rest =>
      cases acquire with
      | acquire _ loaned acquired acquiredExact =>
          cases rest with
          | next release rest =>
              cases release with
              | completeReturn _ returned released releasedExact =>
                  cases rest with
                  | next restore rest =>
                      cases restore with
                      | closeReturn _ _ restored restoredExact =>
                          cases rest with
                          | done =>
                              refine ⟨acquired, Or.inl ?_⟩
                              simp only [actions, CallFrameRun.actions]
                              have releaseExact : released = acquired :=
                                releasedExact.symm.trans acquiredExact
                              subst released
                              subst restored
                              simp [CallFrameTransition.action, acquiredExact]
                          | next impossible _ => cases impossible
              | unwind _ unwinding released releasedExact =>
                  cases rest with
                  | next restore rest =>
                      cases restore with
                      | closeUnwind _ _ restored restoredExact =>
                          cases rest with
                          | done =>
                              refine ⟨acquired, Or.inr ?_⟩
                              simp only [actions, CallFrameRun.actions]
                              have releaseExact : released = acquired :=
                                releasedExact.symm.trans acquiredExact
                              subst released
                              subst restored
                              simp [CallFrameTransition.action, acquiredExact]
                          | next impossible _ => cases impossible

end CallFrameSession

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
