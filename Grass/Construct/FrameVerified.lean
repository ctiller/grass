import Grass.Construct.FrameSource
import Grass.Construct.Fragment.Verified

/-!
# Proof-bearing frame backend seam

`FrameVerifiedBackend` requires a machine owner to supply each
`VerifiedFragment` and an equality to the corresponding transparent frame
source. The construction layer merely projects those proofs through `enter`,
`leave`, `save`, `restore`, `spill`, and `reload`; it cannot synthesize local correctness.
-/

namespace Grass.Construct

open Grass.CFG Grass.ISA.X86 Grass.Construct.Layout Grass.Construct.Fragment

universe u v w

/-- A stack object together with evidence that it belongs to a checked frame. -/
structure FrameObjectRef {profile : LayoutProfile}
    (frame : CheckedWin64Frame profile) where
  object : StackObject profile
  member : object ∈ frame.plan.layout.objects

namespace FrameObjectRef

variable {profile : LayoutProfile} {frame : CheckedWin64Frame profile}

/-- Post-prologue RSP-relative offset of a checked local object. -/
def absoluteOffset (slot : FrameObjectRef frame) : Nat :=
  frame.plan.shadowBytes + frame.plan.stackArgumentBytes + slot.object.offset

end FrameObjectRef

/-- Machine-supplied verified implementations of generic frame operations. -/
structure FrameVerifiedBackend (Instruction : Type u) (State : Type v)
    (Effect : Type w) (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  source : FrameSourceBackend Instruction
  saveContract : {profile : LayoutProfile} → CheckedWin64Frame profile → BlockContract State
  restoreContract : {profile : LayoutProfile} → CheckedWin64Frame profile → BlockContract State
  enterContract : {profile : LayoutProfile} → CheckedWin64Frame profile → BlockContract State
  leaveContract : {profile : LayoutProfile} → CheckedWin64Frame profile → BlockContract State
  slotContract : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    FrameObjectRef frame → Gpr → BlockContract State
  saveVerified : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    VerifiedFragment semantics effectModel (saveContract frame)
  restoreVerified : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    VerifiedFragment semantics effectModel (restoreContract frame)
  enterVerified : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    VerifiedFragment semantics effectModel (enterContract frame)
  leaveVerified : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    VerifiedFragment semantics effectModel (leaveContract frame)
  spillVerified : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    (slot : FrameObjectRef frame) → (register : Gpr) →
    VerifiedFragment semantics effectModel (slotContract frame slot register)
  reloadVerified : {profile : LayoutProfile} → (frame : CheckedWin64Frame profile) →
    (slot : FrameObjectRef frame) → (register : Gpr) →
    VerifiedFragment semantics effectModel (slotContract frame slot register)
  saveSourceExact : ∀ {profile} (frame : CheckedWin64Frame profile),
    (saveVerified frame).source = source.save frame
  restoreSourceExact : ∀ {profile} (frame : CheckedWin64Frame profile),
    (restoreVerified frame).source = source.restore frame
  enterSourceExact : ∀ {profile} (frame : CheckedWin64Frame profile),
    (enterVerified frame).source = source.enter frame
  leaveSourceExact : ∀ {profile} (frame : CheckedWin64Frame profile),
    (leaveVerified frame).source = source.leave frame
  spillSourceExact : ∀ {profile} (frame : CheckedWin64Frame profile)
    (slot : FrameObjectRef frame) (register : Gpr),
    (spillVerified frame slot register).source =
      .literal (source.spill register slot.absoluteOffset)
  reloadSourceExact : ∀ {profile} (frame : CheckedWin64Frame profile)
    (slot : FrameObjectRef frame) (register : Gpr),
    (reloadVerified frame slot register).source =
      .literal (source.reload register slot.absoluteOffset)

namespace FrameVerifiedBackend

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State} {effectModel : EffectModel Instruction Effect}

/-- Transparent verified saved-register projection. -/
def save (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    {profile : LayoutProfile} (frame : CheckedWin64Frame profile) :=
  backend.saveVerified frame

/-- Transparent verified saved-register restoration projection. -/
def restore (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    {profile : LayoutProfile} (frame : CheckedWin64Frame profile) :=
  backend.restoreVerified frame

/-- Transparent verified prologue projection. -/
def enter (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    {profile : LayoutProfile} (frame : CheckedWin64Frame profile) :=
  backend.enterVerified frame

/-- Transparent verified epilogue projection. -/
def leave (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    {profile : LayoutProfile} (frame : CheckedWin64Frame profile) :=
  backend.leaveVerified frame

/-- Transparent verified spill projection for a checked local object. -/
def spill (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    {profile : LayoutProfile} (frame : CheckedWin64Frame profile)
    (slot : FrameObjectRef frame) (register : Gpr) :=
  backend.spillVerified frame slot register

/-- Transparent verified reload projection for a checked local object. -/
def reload (backend : FrameVerifiedBackend Instruction State Effect semantics effectModel)
    {profile : LayoutProfile} (frame : CheckedWin64Frame profile)
    (slot : FrameObjectRef frame) (register : Gpr) :=
  backend.reloadVerified frame slot register

end FrameVerifiedBackend

end Grass.Construct
