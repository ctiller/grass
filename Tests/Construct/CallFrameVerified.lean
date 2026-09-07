import Grass.Construct.CallFrameVerified

namespace Grass.Tests.Construct.CallFrameVerified

open Grass Grass.Core Grass.Construct Grass.Construct.Layout Grass.ISA.X86

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [⟨⟨"local"⟩, ⟨16, 16⟩, 0, root⟩], 16, 16, 128⟩
private def plan : Win64FramePlan profile := ⟨layout, [.rbx], 0, 32, 48⟩
private def frame : CheckedWin64Frame profile := ⟨plan, by native_decide⟩
private def call : Win64CallFrame profile := ⟨plan⟩
private def preparedUse : CallFrameUse profile := ⟨call, .prepared, [], [.rbx]⟩
private def closedUse : CallFrameUse profile := ⟨call, .closed, [], []⟩

private def prepared : CheckedCallFrameUse frame .prepared :=
  ⟨preparedUse, rfl, rfl, by native_decide⟩
private def closed : CheckedCallFrameUse frame .closed :=
  ⟨closedUse, rfl, rfl, by native_decide⟩
private def session : CallFrameSession frame := ⟨prepared, closed⟩

example : session.prepared.use.liveCallLoans = [] := rfl
example : session.prepared.use.restoreObligations = [.rbx] := rfl
example : session.closed.use.liveCallLoans = [] := rfl
example : session.closed.use.restoreObligations = [] := rfl

end Grass.Tests.Construct.CallFrameVerified
