import Grass.Construct.FrameSource

namespace Grass.Tests.Construct.FrameSource

open Grass Grass.Core Grass.Construct Grass.Construct.Layout Grass.Construct.Fragment Grass.ISA.X86

private inductive Instruction where
  | push (r : Gpr) | pop (r : Gpr) | sub (n : Nat) | add (n : Nat)
  | spill (r : Gpr) (offset : Nat) | reload (r : Gpr) (offset : Nat)
deriving Repr, DecidableEq

private def backend : FrameSourceBackend Instruction where
  push := .push
  pop := .pop
  subtractRsp n := [.sub n]
  addRsp n := [.add n]
  spill r offset := [.spill r offset]
  reload r offset := [.reload r offset]

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [⟨⟨"slot"⟩, ⟨8, 8⟩, 0, root⟩], 16, 16, 128⟩

private def plan : Win64FramePlan profile :=
  ⟨layout, [.rbx, .r12], 0, 32, 56⟩

private def frame : CheckedWin64Frame profile :=
  ⟨plan, by decide⟩

example : (backend.save frame).expand = [.push .rbx, .push .r12] := by decide
example : (backend.restore frame).expand = [.pop .r12, .pop .rbx] := by decide
example : (backend.enter frame).expand =
    [.push .rbx, .push .r12, .sub frame.plan.subtracted] := by decide
example : (backend.leave frame).expand =
    [.add frame.plan.subtracted, .pop .r12, .pop .rbx] := by decide
example : (backend.spill? frame ⟨"slot"⟩ .rax).map Source.expand =
    some [.spill .rax 32] := by decide
example : (backend.reload? frame ⟨"slot"⟩ .rax).map Source.expand =
    some [.reload .rax 32] := by decide
example : backend.reload? frame ⟨"missing"⟩ .rax = none := by decide

end Grass.Tests.Construct.FrameSource
