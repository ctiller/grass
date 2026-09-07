import Grass.ABI.Win64.Convention
import Grass.Construct.Layout.Stack

/-!
# Checked Win64 frame selection

`deriveWin64Frame` combines a checked lexical `StackLayout` with explicit saved
registers and stack-argument space. Success returns `CheckedWin64Frame`, whose
certificate enforces the existing `Grass.ABI.Win64.AlignedForCall` predicate and
the existing shadow-space and volatility tables.
-/

namespace Grass.Construct

open Grass.ISA.X86 Grass.ABI.Win64 Grass.Construct.Layout

/-- Selected Win64 frame quantities before instruction generation. -/
structure Win64FramePlan (profile : LayoutProfile) where
  layout : StackLayout profile
  saved : List Gpr
  stackArgumentBytes : Nat
  shadowBytes : Nat
  subtracted : Nat
deriving Repr, DecidableEq

namespace Win64FramePlan

variable {profile : LayoutProfile}

def savedValid (plan : Win64FramePlan profile) : Bool :=
  plan.saved.all fun register => register != .rsp && volatility register == .nonvolatile

def wellFormed (plan : Win64FramePlan profile) : Bool :=
  plan.layout.wellFormed &&
  decide plan.saved.Nodup &&
  plan.savedValid &&
  decide (plan.stackArgumentBytes % 8 = 0) &&
  decide (plan.shadowBytes = shadowSpaceBytes) &&
  decide (plan.layout.size + plan.stackArgumentBytes + plan.shadowBytes ≤ plan.subtracted) &&
  decide (AlignedForCall plan.saved.length plan.subtracted)

def WellFormed (plan : Win64FramePlan profile) : Prop := plan.wellFormed = true

instance (plan : Win64FramePlan profile) : Decidable plan.WellFormed :=
  inferInstanceAs (Decidable (plan.wellFormed = true))

end Win64FramePlan

/-- A selected frame paired with its checked Win64 structural certificate. -/
structure CheckedWin64Frame (profile : LayoutProfile) where
  plan : Win64FramePlan profile
  valid : plan.WellFormed

/-- Why `deriveWin64Frame` rejected a frame request. -/
inductive Win64FrameError where
  | invalidLayout
  | duplicateSaved
  | invalidSaved (index : Nat)
  | invalidStackArgumentBytes (bytes : Nat)
  | noAlignedPlan
deriving Repr, DecidableEq

private def firstInvalidSaved? : Nat → List Gpr → Option Nat
  | _, [] => none
  | index, register :: rest =>
      if register != .rsp ∧ volatility register = .nonvolatile then
        firstInvalidSaved? (index + 1) rest
      else some index

private def firstAlignedSubtraction? (pushes base : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      let candidate := base + (16 - fuel - 1)
      if AlignedForCall pushes candidate then some candidate
      else firstAlignedSubtraction? pushes base fuel

/-- Derive a checked frame, adding at most fifteen bytes of alignment padding. -/
def deriveWin64Frame {profile : LayoutProfile} (layout : StackLayout profile)
    (saved : List Gpr) (stackArgumentBytes : Nat) :
    Except Win64FrameError (CheckedWin64Frame profile) :=
  if _layout : layout.WellFormed then
    if _unique : saved.Nodup then
      match firstInvalidSaved? 0 saved with
      | some index => .error (.invalidSaved index)
      | none =>
          if _args : stackArgumentBytes % 8 = 0 then
            let base := layout.size + stackArgumentBytes + shadowSpaceBytes
            match firstAlignedSubtraction? saved.length base 16 with
            | none => .error .noAlignedPlan
            | some subtracted =>
                let plan : Win64FramePlan profile :=
                  ⟨layout, saved, stackArgumentBytes, shadowSpaceBytes, subtracted⟩
                if valid : plan.WellFormed then .ok ⟨plan, valid⟩
                else .error .noAlignedPlan
          else .error (.invalidStackArgumentBytes stackArgumentBytes)
    else .error .duplicateSaved
  else .error .invalidLayout

end Grass.Construct
