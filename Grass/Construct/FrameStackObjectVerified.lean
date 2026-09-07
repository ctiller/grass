import Grass.Construct.FrameStackObject
import Grass.Construct.Fragment.Verified

/-!
# Proof-bearing Win64 frame stack-slice backend seam

`FrameStackObjectVerifiedBackend` requires machine-supplied verified load/store
fragments over checked Win64 frame slices. Its source equalities bind each
fragment to the exact post-prologue RSP-relative source derived by
`StackObjectSourceBackend.loadFrame` or `StackObjectSourceBackend.storeFrame`.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Layout Grass.Construct.Fragment

universe u v w x

/-- Machine-supplied verified implementations of Win64 frame-slice operations. -/
structure FrameStackObjectVerifiedBackend (Instruction : Type u) (Operand : Type v)
    (State : Type w) (Effect : Type x) (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  source : StackObjectSourceBackend Instruction Operand
  loadContract : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    {slot : StackObjectRef frame.checkedLayout} →
    CheckedStackSlice slot → Operand → BlockContract State
  storeContract : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    {slot : StackObjectRef frame.checkedLayout} →
    CheckedStackSlice slot → Operand → BlockContract State
  loadVerified : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    {slot : StackObjectRef frame.checkedLayout} →
    (slice : CheckedStackSlice slot) → (destination : Operand) →
    VerifiedFragment semantics effectModel (loadContract frame slice destination)
  storeVerified : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    {slot : StackObjectRef frame.checkedLayout} →
    (slice : CheckedStackSlice slot) → (sourceOperand : Operand) →
    VerifiedFragment semantics effectModel (storeContract frame slice sourceOperand)
  loadSourceExact : ∀ {profile} (frame : CheckedWin64Frame profile)
    {slot : StackObjectRef frame.checkedLayout} (slice : CheckedStackSlice slot)
    (destination : Operand),
    (loadVerified frame slice destination).source = source.loadFrame frame slice destination
  storeSourceExact : ∀ {profile} (frame : CheckedWin64Frame profile)
    {slot : StackObjectRef frame.checkedLayout} (slice : CheckedStackSlice slot)
    (sourceOperand : Operand),
    (storeVerified frame slice sourceOperand).source = source.storeFrame frame slice sourceOperand

namespace FrameStackObjectVerifiedBackend

variable {Instruction : Type u} {Operand : Type v} {State : Type w} {Effect : Type x}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {profile : LayoutProfile}

/-- Transparent verified frame-slice load projection. -/
def load
    (backend : FrameStackObjectVerifiedBackend Instruction Operand State Effect
      semantics effectModel)
    (frame : CheckedWin64Frame profile) {slot : StackObjectRef frame.checkedLayout}
    (slice : CheckedStackSlice slot) (destination : Operand) :=
  backend.loadVerified frame slice destination

/-- Transparent verified frame-slice store projection. -/
def store
    (backend : FrameStackObjectVerifiedBackend Instruction Operand State Effect
      semantics effectModel)
    (frame : CheckedWin64Frame profile) {slot : StackObjectRef frame.checkedLayout}
    (slice : CheckedStackSlice slot) (sourceOperand : Operand) :=
  backend.storeVerified frame slice sourceOperand

end FrameStackObjectVerifiedBackend

end Grass.Construct
