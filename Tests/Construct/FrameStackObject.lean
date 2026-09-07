import Grass.Construct.FrameStackObject

/-!
# Checked Win64 frame stack-slice fixtures

Fixtures pin exact local-layout reuse, post-prologue RSP-relative range
derivation, allocation containment, and transparent source expansion.
-/

namespace Grass.Tests.Construct.FrameStackObject

open Grass.Core Grass.Memory Grass.Construct Grass.Construct.Layout
  Grass.Construct.Fragment Grass.ISA.X86

private inductive Operand where
  | register (name : String)
deriving Repr, DecidableEq

private inductive Instruction where
  | load (range : ByteRange) (destination : Operand)
  | store (range : ByteRange) (source : Operand)
deriving Repr, DecidableEq

private def backend : StackObjectSourceBackend Instruction Operand where
  loadAt range destination := [.load range destination]
  storeAt range source := [.store range source]

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def word : Layout.StackObject profile :=
  ⟨⟨"word"⟩, ⟨8, 8⟩, 0, root⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [word], 16, 16, 64⟩
private def plan : Win64FramePlan profile :=
  ⟨layout, [.rbx], 16, 32, 64⟩
private def frame : CheckedWin64Frame profile := ⟨plan, by decide⟩
private def slot : StackObjectRef frame.checkedLayout := ⟨word, by decide⟩
private def slice : CheckedStackSlice slot := ⟨⟨2, 4⟩, by decide⟩
private def destination : Operand := .register "rax"
private def source : Operand := .register "rbx"

example : frame.checkedLayout.layout = frame.plan.layout := rfl
example : frame.localBase = 48 := rfl
example : frame.stackRange slice = ⟨50, 4⟩ := rfl
example : (frame.stackRange slice).WithinBound frame.plan.subtracted :=
  frame.stackRange_withinSubtracted slice
example : (backend.loadFrame frame slice destination).expand =
    [.load ⟨50, 4⟩ destination] := by decide
example : (backend.storeFrame frame slice source).expand =
    [.store ⟨50, 4⟩ source] := by decide

private def checkedByName :
    Except StackObjectError (NamedCheckedStackSlice frame.checkedLayout ⟨"word"⟩) :=
  frame.checkStackSlice ⟨"word"⟩ 2 4

example : checkedByName.map (fun found => frame.stackRange found.checkedSlice) =
    .ok ⟨50, 4⟩ := by rfl

end Grass.Tests.Construct.FrameStackObject
