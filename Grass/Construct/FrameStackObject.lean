import Grass.Construct.Frame
import Grass.Construct.StackObjectSource

/-!
# Checked stack-object slices in a Win64 frame

`CheckedWin64Frame.checkedLayout` exposes the exact checked local layout already
carried by a valid frame plan. `CheckedWin64Frame.stackRange` adds the derived
shadow and stack-argument base to a checked local slice, and
`CheckedWin64Frame.stackRange_withinSubtracted` proves the resulting range lies
within the selected post-prologue stack allocation.
-/

namespace Grass.Construct

open Grass.Core Grass.Memory Grass.Construct.Layout Grass.Construct.Fragment

universe u v

namespace CheckedWin64Frame

variable {profile : LayoutProfile}

/-- The exact local layout carried by a checked Win64 frame. -/
def checkedLayout (frame : CheckedWin64Frame profile) : CheckedStackLayout profile where
  layout := frame.plan.layout
  valid := by
    have valid := frame.valid
    simp [Win64FramePlan.WellFormed, Win64FramePlan.wellFormed] at valid
    exact valid.1.1.1.1.1.1

/-- Post-prologue RSP-relative base of the checked local-layout region. -/
def localBase (frame : CheckedWin64Frame profile) : Nat :=
  frame.plan.shadowBytes + frame.plan.stackArgumentBytes

/-- Post-prologue RSP-relative range derived from one checked local slice. -/
def stackRange (frame : CheckedWin64Frame profile)
    {slot : StackObjectRef frame.checkedLayout} (slice : CheckedStackSlice slot) :
    ByteRange :=
  ⟨frame.localBase + slice.absoluteRange.start, slice.absoluteRange.size⟩

/-- Find and check a nominal local slice in this frame's exact checked layout. -/
def checkStackSlice (frame : CheckedWin64Frame profile) (name : Name)
    (offset size : Nat) :
    Except StackObjectError (NamedCheckedStackSlice frame.checkedLayout name) :=
  Grass.Construct.checkStackSlice frame.checkedLayout name offset size

/-- Every derived stack range lies within the selected frame subtraction. -/
theorem stackRange_withinSubtracted (frame : CheckedWin64Frame profile)
    {slot : StackObjectRef frame.checkedLayout} (slice : CheckedStackSlice slot) :
    (frame.stackRange slice).WithinBound frame.plan.subtracted := by
  have sliceBound := slice.withinLayout
  have planValid := frame.valid
  simp [Win64FramePlan.WellFormed, Win64FramePlan.wellFormed] at planValid
  simp [stackRange, localBase, checkedLayout, CheckedStackSlice.absoluteRange,
    StackSlice.absoluteRange, ByteRange.withinBound_def] at sliceBound ⊢
  omega

end CheckedWin64Frame

namespace StackObjectSourceBackend

variable {Instruction : Type u} {Operand : Type v} {profile : LayoutProfile}

/-- Transparent source for loading a checked slice at its Win64 frame offset. -/
def loadFrame (backend : StackObjectSourceBackend Instruction Operand)
    (frame : CheckedWin64Frame profile)
    {slot : StackObjectRef frame.checkedLayout} (slice : CheckedStackSlice slot)
    (destination : Operand) : Source Instruction :=
  .literal (backend.loadAt (frame.stackRange slice) destination)

/-- Transparent source for storing a checked slice at its Win64 frame offset. -/
def storeFrame (backend : StackObjectSourceBackend Instruction Operand)
    (frame : CheckedWin64Frame profile)
    {slot : StackObjectRef frame.checkedLayout} (slice : CheckedStackSlice slot)
    (source : Operand) : Source Instruction :=
  .literal (backend.storeAt (frame.stackRange slice) source)

@[simp] theorem loadFrame_expand
    (backend : StackObjectSourceBackend Instruction Operand)
    (frame : CheckedWin64Frame profile)
    {slot : StackObjectRef frame.checkedLayout} (slice : CheckedStackSlice slot)
    (destination : Operand) :
    (backend.loadFrame frame slice destination).expand =
      backend.loadAt (frame.stackRange slice) destination := by
  simp [loadFrame]

@[simp] theorem storeFrame_expand
    (backend : StackObjectSourceBackend Instruction Operand)
    (frame : CheckedWin64Frame profile)
    {slot : StackObjectRef frame.checkedLayout} (slice : CheckedStackSlice slot)
    (source : Operand) :
    (backend.storeFrame frame slice source).expand =
      backend.storeAt (frame.stackRange slice) source := by
  simp [storeFrame]

end StackObjectSourceBackend

end Grass.Construct
