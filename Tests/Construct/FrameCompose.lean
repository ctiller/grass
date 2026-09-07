import Grass.Construct.FrameCompose

namespace Grass.Tests.Construct.FrameCompose

open Grass.CFG Grass.Construct Grass.Construct.Layout Grass.Construct.Fragment

universe u v w

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State} {effectModel : EffectModel Instruction Effect}
  {profile : LayoutProfile}
  (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
  (laws : SequentialLaws semantics effectModel)
  (frame : CheckedWin64Frame profile)
  {bodyContract : BlockContract State}
  (body : VerifiedFragment semantics effectModel bodyContract)
  (enterBoundary : BoundaryCompatible (backend.enterContract frame) bodyContract)
  (leaveBoundary : BoundaryCompatible
    (thenContract (backend.enterContract frame) bodyContract)
    (backend.leaveContract frame))

example :
    (backend.withFrame laws frame body enterBoundary leaveBoundary).source.expand =
      (backend.enter frame).source.expand ++ body.source.expand ++
        (backend.leave frame).source.expand :=
  backend.withFrame_expand laws frame body enterBoundary leaveBoundary

example :
    (backend.withFrame laws frame body enterBoundary leaveBoundary).effects =
      effectModel.derive
        (backend.withFrame laws frame body enterBoundary leaveBoundary).source.expand :=
  (backend.withFrame laws frame body enterBoundary leaveBoundary).effectsExact

end Grass.Tests.Construct.FrameCompose
