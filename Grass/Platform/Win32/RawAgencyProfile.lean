import Grass.Platform.Win32.RawStep

/-! Selected caller-relative agency for the fixed Win32 Hello profile.
Provider service by the selected provider, API results and completed exit
observations are environment-owned; compiled caller CPU work and API entry
are program-owned. This is explicit profile semantics, with native applicability
owed. It is not a classification for arbitrary composed program-owned providers.
-/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Op
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- The selected Hello profile's external-agency interpretation. This definition
classifies choices only and does not assert their enabledness or wait permission. -/
def helloExternalChoice (environment : ConsoleEnvironment) : Choice → Prop
  | .cpu _ | .apiEntry _ _ => False
  | .providerService _ agent _ => agent = environment.provider
  | .providerReturn _ _ _ _ | .stdoutResult _ _ _ | .exitObservation _ _ => True

/-- `pending_external` derives external ownership for every actual outgoing
edge at this exact selected pending cut. It constructs no additional step. -/
theorem RawStep.pending_external {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {graph nextGraph : Graph} {before after : RawState} {choice : Choice} {event : Event}
    {call : CallProtocol.CallId}
    (step : RawStep loaded realization environment interpretation graph before choice event after nextGraph)
    (pending : before.control = .pending call environment.caller environment.provider) :
    helloExternalChoice environment choice := by
  cases step with
  | writeFileEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans pending)
  | getStdHandleEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans pending)
  | exitProcessEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans pending)
  | writeFileReturn => trivial
  | getStdHandleReturn => trivial
  | completedExit => trivial
  | service receipt agreement kind priorCausal nextCausal =>
      exact (Control.pending.inj (receipt.control.symm.trans pending)).2.2
  | cpuCompleted control selected evaluated completed agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)
  | cpuFailure control selected evaluated mapped agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)
  | cpuUncovered control selected nonNormal evaluated agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)

/-- `cpu_not_external` prevents caller CPU work from using this profile's
external-agency classification, regardless of its event's observation. -/
theorem cpu_not_external (environment : ConsoleEnvironment)
    (choice : Grass.ISA.X86.Execution.CheckedChoice) :
    ¬ helloExternalChoice environment (.cpu choice) := id

end Grass.Platform.Win32.Raw
