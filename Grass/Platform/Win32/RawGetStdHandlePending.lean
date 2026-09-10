import Grass.Platform.Win32.RawStep

/-! Outgoing-choice inversion at a GetStdHandle pending occurrence. -/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- An actual edge from a pending occurrence whose runtime entry is
`GetStdHandle` can only select the corresponding stdout-result choice. This is
an inversion theorem and supplies no reply or checker-totality witness. -/
theorem RawStep.getStdHandle_pending_choice {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {graph nextGraph : Graph} {before after : RawState} {choice : Choice} {event : Event}
    {call : CallProtocol.CallId} {caller provider : ContextId} {frame : ReturnFrame}
    (step : RawStep loaded realization environment interpretation graph before choice event after nextGraph)
    (control : before.control = .pending call caller provider)
    (runtime : before.calls.lookup call = some (.getStdHandle frame)) :
    ∃ (gpr : Grass.ISA.X86.Gpr → BitVec 64) (rflags : BitVec 64),
      choice = .stdoutResult call gpr rflags := by
  cases step with
  | writeFileEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans control)
  | getStdHandleEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans control)
  | writeFileReturn evaluated observed returned completion completed actualCaller
      providerContext agreement =>
      have sameControl := observed.control.symm.trans control
      injection sameControl
      subst_vars
      have conflict := Option.some.inj (observed.link.runtimeLookup.symm.trans runtime)
      cases conflict
  | @getStdHandleReturn graph nextGraph entryBefore prior afterFetch afterRead afterStore
      displacement receipt agent entered evaluated gpr rflags observed completion completed agreement =>
      have actualControl : (entered.afterRaw prior).control =
          .pending entered.handoff.call entered.handoff.caller agent := by
        rfl
      have sameControl := actualControl.symm.trans control
      injection sameControl
      subst_vars
      exact ⟨_, _, rfl⟩
  | exitProcessEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans control)
  | completedExit completion completed agreement =>
      have sameControl := completion.controlExact.symm.trans control
      injection sameControl
      subst_vars
      have conflict := Option.some.inj (completion.runtimeExact.symm.trans runtime)
      cases conflict
  | service receipt agreement kind priorCausal nextCausal =>
      have sameControl := receipt.control.symm.trans control
      injection sameControl
      subst_vars
      have conflict := Option.some.inj (receipt.runtimeLookup.symm.trans runtime)
      cases conflict
  | cpuCompleted actualControl selected evaluated completed agreement kind =>
      exact Control.noConfusion (actualControl.symm.trans control)
  | cpuFailure actualControl selected evaluated mapped agreement kind =>
      exact Control.noConfusion (actualControl.symm.trans control)
  | cpuUncovered actualControl selected nonNormal evaluated agreement kind =>
      exact Control.noConfusion (actualControl.symm.trans control)

end Grass.Platform.Win32.Raw
