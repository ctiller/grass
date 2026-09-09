import Grass.Platform.Win32.GetStdHandleRuntime

namespace Grass.Tests.Win32GetStdHandleRuntime

open Grass.Platform.Win32 Grass.Platform.Win32.GetStdHandle

example (state : Grass.ISA.X86.Execution.State) :
    selector state = BitVec.setWidth 32 (state.gpr .rcx) := rfl

example (returnSlot homeSlot : Grass.Platform.Win32.WriteFile.Argument) :
    (stackRequests returnSlot homeSlot).length = 2 := by simp [stackRequests]

example {image inputs loaded before afterFetch afterRead afterStore displacement receipt agent}
    (handoff : @CallHandoff image inputs loaded before afterFetch afterRead afterStore
      displacement receipt agent) (calls : CallRuntimeTable) :
    (handoff.afterRaw calls).calls.lookup handoff.handoff.call =
      some (.getStdHandle handoff.frame) := by simp

example {image inputs loaded before afterFetch afterRead afterStore displacement agent}
    (handoff : @RawCallHandoff image inputs loaded before afterFetch afterRead afterStore
      displacement agent) {other : Grass.Op.CallProtocol.CallId}
    (different : other ≠ handoff.entered.handoff.call) :
    handoff.after.calls.lookup other = before.calls.lookup other :=
  handoff.after_other different

end Grass.Tests.Win32GetStdHandleRuntime
