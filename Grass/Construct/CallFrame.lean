import Grass.Construct.Frame

/-!
# Win64 call-frame regions and phases

`Win64CallFrame.wellFormed` derives shadow, stack-argument, and local regions
from a checked `Win64FramePlan`. `CallFrameUse.wellFormed` separately tracks the
call-loan and saved-register restoration lifecycle, so a structurally aligned
frame cannot be mistaken for a closed call frame.
-/

namespace Grass.Construct

open Grass.Core Grass.Memory Grass.Construct.Layout

/-- Stable phases of one call-frame use. -/
inductive CallFramePhase where
  | prepared | loaned | returned | unwinding | closed
deriving Repr, DecidableEq

/-- ABI regions derived from a selected Win64 frame plan. -/
structure Win64CallFrame (profile : LayoutProfile) where
  frame : Win64FramePlan profile
deriving Repr, DecidableEq

namespace Win64CallFrame

variable {profile : LayoutProfile}

def shadowRange (call : Win64CallFrame profile) : ByteRange :=
  ⟨0, call.frame.shadowBytes⟩

def stackArgumentRange (call : Win64CallFrame profile) : ByteRange :=
  ⟨call.frame.shadowBytes, call.frame.stackArgumentBytes⟩

def localBase (call : Win64CallFrame profile) : Nat :=
  call.frame.shadowBytes + call.frame.stackArgumentBytes

def localRange (call : Win64CallFrame profile) : ByteRange :=
  ⟨call.localBase, call.frame.layout.size⟩

def wellFormed (call : Win64CallFrame profile) : Bool :=
  call.frame.wellFormed &&
  decide (call.shadowRange.Disjoint call.stackArgumentRange) &&
  decide (call.stackArgumentRange.Disjoint call.localRange) &&
  decide (call.localRange.WithinBound call.frame.subtracted)

def WellFormed (call : Win64CallFrame profile) : Prop := call.wellFormed = true

instance (call : Win64CallFrame profile) : Decidable call.WellFormed :=
  inferInstanceAs (Decidable (call.wellFormed = true))

end Win64CallFrame

/-- Explicit resource ledger for one call-frame phase. -/
structure CallFrameUse (profile : LayoutProfile) where
  call : Win64CallFrame profile
  phase : CallFramePhase
  liveCallLoans : List Name
  restoreObligations : List Grass.ISA.X86.Gpr
deriving Repr, DecidableEq

namespace CallFrameUse

variable {profile : LayoutProfile}

def lifecycleWellFormed (use : CallFrameUse profile) : Bool :=
  match use.phase with
  | .prepared | .returned | .unwinding =>
      use.liveCallLoans.isEmpty && decide (use.restoreObligations = use.call.frame.saved)
  | .loaned =>
      !use.liveCallLoans.isEmpty && decide (use.restoreObligations = use.call.frame.saved)
  | .closed =>
      use.liveCallLoans.isEmpty && use.restoreObligations.isEmpty

def wellFormed (use : CallFrameUse profile) : Bool :=
  use.call.wellFormed && decide use.liveCallLoans.Nodup && use.lifecycleWellFormed

def WellFormed (use : CallFrameUse profile) : Prop := use.wellFormed = true

instance (use : CallFrameUse profile) : Decidable use.WellFormed :=
  inferInstanceAs (Decidable (use.wellFormed = true))

end CallFrameUse

end Grass.Construct
