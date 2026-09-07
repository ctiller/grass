import Grass.Construct.FrameVerified
import Grass.Construct.Fragment.Compose

/-!
# Verified frame composition

`withFrame` composes a backend-supplied verified prologue, an authored verified
body, and a backend-supplied verified epilogue. It consumes
`Fragment.SequentialLaws` and explicit boundary proofs; construction neither
guesses an effect algebra nor weakens an exit family.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Layout Grass.Construct.Fragment

universe u v w

namespace FrameVerifiedBackend

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State} {effectModel : EffectModel Instruction Effect}
  {profile : LayoutProfile}

/-- Wrap a verified body in the exact verified frame entry and exit fragments. -/
def withFrame
    (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    (laws : SequentialLaws semantics effectModel)
    (frame : CheckedWin64Frame profile)
    {bodyContract : BlockContract State}
    (body : VerifiedFragment semantics effectModel bodyContract)
    (enterBoundary : BoundaryCompatible (backend.enterContract frame) bodyContract)
    (leaveBoundary : BoundaryCompatible
      (thenContract (backend.enterContract frame) bodyContract)
      (backend.leaveContract frame)) :
    VerifiedFragment semantics effectModel
      (thenContract (thenContract (backend.enterContract frame) bodyContract)
        (backend.leaveContract frame)) :=
  (backend.enter frame).compose laws body enterBoundary |>.compose laws
    (backend.leave frame) leaveBoundary

/-- `withFrame_expand` pins prologue, body, and epilogue instruction order. -/
@[simp] theorem withFrame_expand
    (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    (laws : SequentialLaws semantics effectModel)
    (frame : CheckedWin64Frame profile)
    {bodyContract : BlockContract State}
    (body : VerifiedFragment semantics effectModel bodyContract)
    (enterBoundary : BoundaryCompatible (backend.enterContract frame) bodyContract)
    (leaveBoundary : BoundaryCompatible
      (thenContract (backend.enterContract frame) bodyContract)
      (backend.leaveContract frame)) :
    (backend.withFrame laws frame body enterBoundary leaveBoundary).source.expand =
      (backend.enter frame).source.expand ++ body.source.expand ++
        (backend.leave frame).source.expand := by
  simp [withFrame]

end FrameVerifiedBackend

end Grass.Construct
