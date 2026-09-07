import Grass.Construct.CallFrame
import Grass.Construct.Fragment.Source

/-!
# Transparent frame instruction sources

`FrameSourceBackend` supplies machine-owned instruction constructors.
`enter`, `leave`, `spill?`, and `reload?` only assemble inspectable
`Fragment.Source` values from a checked frame; they do not manufacture a
`Fragment.VerifiedFragment` or any semantic certificate.
-/

namespace Grass.Construct

open Grass.Core Grass.ISA.X86 Grass.Construct.Layout Grass.Construct.Fragment

universe u

/-- Machine-specific instruction constructors consumed by generic frame assembly. -/
structure FrameSourceBackend (Instruction : Type u) where
  push : Gpr → Instruction
  pop : Gpr → Instruction
  subtractRsp : Nat → List Instruction
  addRsp : Nat → List Instruction
  spill : Gpr → Nat → List Instruction
  reload : Gpr → Nat → List Instruction

namespace FrameSourceBackend

variable {Instruction : Type u} {profile : LayoutProfile}

/-- Prologue source in saved-register order, followed by stack subtraction. -/
def enter (backend : FrameSourceBackend Instruction)
    (frame : CheckedWin64Frame profile) : Source Instruction :=
  .sequence [
    .literal (frame.plan.saved.map backend.push),
    .literal (backend.subtractRsp frame.plan.subtracted)
  ]

/-- Epilogue source restores stack space, then registers in reverse order. -/
def leave (backend : FrameSourceBackend Instruction)
    (frame : CheckedWin64Frame profile) : Source Instruction :=
  .sequence [
    .literal (backend.addRsp frame.plan.subtracted),
    .literal (frame.plan.saved.reverse.map backend.pop)
  ]

private def object? (frame : CheckedWin64Frame profile) (name : Name) :=
  frame.plan.layout.objects.find? (fun object => object.name == name)

/-- Spill to a declared local object, using its exact frame-relative offset. -/
def spill? (backend : FrameSourceBackend Instruction)
    (frame : CheckedWin64Frame profile) (name : Name) (register : Gpr) :
    Option (Source Instruction) :=
  (object? frame name).map fun object =>
    let offset := frame.plan.shadowBytes + frame.plan.stackArgumentBytes + object.offset
    .literal (backend.spill register offset)

/-- Reload from a declared local object, using its exact frame-relative offset. -/
def reload? (backend : FrameSourceBackend Instruction)
    (frame : CheckedWin64Frame profile) (name : Name) (register : Gpr) :
    Option (Source Instruction) :=
  (object? frame name).map fun object =>
    let offset := frame.plan.shadowBytes + frame.plan.stackArgumentBytes + object.offset
    .literal (backend.reload register offset)

@[simp] theorem enter_expand (backend : FrameSourceBackend Instruction)
    (frame : CheckedWin64Frame profile) :
    (backend.enter frame).expand =
      frame.plan.saved.map backend.push ++ backend.subtractRsp frame.plan.subtracted := by
  simp [enter]

@[simp] theorem leave_expand (backend : FrameSourceBackend Instruction)
    (frame : CheckedWin64Frame profile) :
    (backend.leave frame).expand =
      backend.addRsp frame.plan.subtracted ++ frame.plan.saved.reverse.map backend.pop := by
  simp [leave]

end FrameSourceBackend

end Grass.Construct
