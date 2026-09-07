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
private def loanedUse : CallFrameUse profile := ⟨call, .loaned, [⟨"call"⟩], [.rbx]⟩
private def returnedUse : CallFrameUse profile := ⟨call, .returned, [], [.rbx]⟩
private def unwindingUse : CallFrameUse profile := ⟨call, .unwinding, [], [.rbx]⟩
private def closedUse : CallFrameUse profile := ⟨call, .closed, [], []⟩

private def prepared : CheckedCallFrameUse frame .prepared :=
  ⟨preparedUse, rfl, rfl, by native_decide⟩
private def loaned : CheckedCallFrameUse frame .loaned :=
  ⟨loanedUse, rfl, rfl, by native_decide⟩
private def returned : CheckedCallFrameUse frame .returned :=
  ⟨returnedUse, rfl, rfl, by native_decide⟩
private def unwinding : CheckedCallFrameUse frame .unwinding :=
  ⟨unwindingUse, rfl, rfl, by native_decide⟩
private def closed : CheckedCallFrameUse frame .closed :=
  ⟨closedUse, rfl, rfl, by native_decide⟩

private def returnRun : CallFrameRun frame prepared closed :=
  .next (.acquire prepared loaned [⟨"call"⟩] rfl)
    (.next (.completeReturn loaned returned [⟨"call"⟩] rfl)
      (.next (.closeReturn returned closed [.rbx] rfl) (.done closed)))

private def unwindRun : CallFrameRun frame prepared closed :=
  .next (.acquire prepared loaned [⟨"call"⟩] rfl)
    (.next (.unwind loaned unwinding [⟨"call"⟩] rfl)
      (.next (.closeUnwind unwinding closed [.rbx] rfl) (.done closed)))

private def session : CallFrameSession frame := ⟨prepared, closed, returnRun⟩
private def unwindSession : CallFrameSession frame := ⟨prepared, closed, unwindRun⟩

example : session.prepared.use.liveCallLoans = [] := rfl
example : session.prepared.use.restoreObligations = [.rbx] := rfl
example : session.closed.use.liveCallLoans = [] := rfl
example : session.closed.use.restoreObligations = [] := rfl
example : unwindSession.closed.use.restoreObligations = [] := rfl

example : returnRun.actions =
    [.acquire [⟨"call"⟩], .releaseReturn [⟨"call"⟩], .restoreReturn [.rbx]] := rfl

example : unwindRun.actions =
    [.acquire [⟨"call"⟩], .releaseUnwind [⟨"call"⟩], .restoreUnwind [.rbx]] := rfl

example : (CallFrameRun.done prepared).append returnRun = returnRun := rfl

example : ¬Nonempty (CallFrameTransition frame prepared closed) := by
  intro transition
  cases transition with
  | intro transition => cases transition

end Grass.Tests.Construct.CallFrameVerified
