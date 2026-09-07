import Grass.Construct.CallFrame

namespace Grass.Tests.Construct.CallFrame

open Grass Grass.Core Grass.Construct Grass.Construct.Layout Grass.ISA.X86

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [⟨⟨"local"⟩, ⟨16, 16⟩, 0, root⟩], 16, 16, 128⟩

private def frame : Win64FramePlan profile :=
  match deriveWin64Frame layout [.rbx] 16 with
  | .ok checked => checked.plan
  | .error _ => ⟨layout, [], 0, 0, 0⟩

private def call : Win64CallFrame profile := ⟨frame⟩

example : call.WellFormed := by decide
example : call.shadowRange = ⟨0, 32⟩ := by decide
example : call.stackArgumentRange = ⟨32, 16⟩ := by decide
example : call.localRange = ⟨48, 16⟩ := by decide

private def prepared : CallFrameUse profile := ⟨call, .prepared, [], [.rbx]⟩
private def loaned : CallFrameUse profile := ⟨call, .loaned, [⟨"call"⟩], [.rbx]⟩
private def returned : CallFrameUse profile := ⟨call, .returned, [], [.rbx]⟩
private def closed : CallFrameUse profile := ⟨call, .closed, [], []⟩

example : prepared.WellFormed := by decide
example : loaned.WellFormed := by decide
example : returned.WellFormed := by decide
example : closed.WellFormed := by decide
example : ¬ ({ loaned with liveCallLoans := [] }).WellFormed := by decide
example : ¬ ({ loaned with liveCallLoans := [⟨"call"⟩, ⟨"call"⟩] }).WellFormed := by
  decide
example : ¬ ({ closed with restoreObligations := [.rbx] }).WellFormed := by decide

end Grass.Tests.Construct.CallFrame
