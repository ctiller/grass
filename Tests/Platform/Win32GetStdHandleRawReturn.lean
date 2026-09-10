import Grass.Platform.Win32.GetStdHandleRawReturn
import Tests.Platform.Win32GetStdHandleReturn
import Tests.Platform.Win32RawStep

/-! Actual Grass Hello CALL followed by the bounded raw GetStdHandle result
edge. The empty graph proves only the partial relation's graph obligations;
it supplies no native or cross-log causal correspondence. -/

namespace Grass.Tests.Win32GetStdHandleRawReturn

open Grass.Core Grass.Std.Logical Grass.ISA.X86
open Grass.Platform.Win32 Grass.Platform.Win32.ExecutionState

private def check (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError "actual GetStdHandle raw return refused or changed its event")

def regressionFor (actual : Grass.Tests.Win32HelloCall.ActualResult)
    (table raw : BitVec 64) : Option Bool :=
  let setup := actual.setup
  let handoff := actual.handoff
  let entered := handoff.entered.entered
  let prior := handoff.preCall.before.calls
  let evaluated := Grass.Tests.Win32GetStdHandleReturn.evaluatedFor handoff
  let environment := Grass.Tests.Win32GetStdHandleReturn.environmentFor
    entered.handoff.caller setup.inputs.independentContext table
  let gpr : Gpr → BitVec 64 := fun register =>
    if register = .rax then raw else entered.reached.machine.gpr register
  let rflags := entered.reached.machine.rflags
  match GetStdHandle.ProviderResult.observe? setup.loaded environment
      entered evaluated prior gpr rflags with
  | .error _ => none
  | .ok observed =>
    match completed : GetStdHandle.Return.complete? observed with
    | .error _ => none
    | .ok completion =>
      let step : Raw.RawStep setup.loaded Grass.Tests.Win32WriteFile.noEffects environment
          [] (entered.afterRaw prior) (.stdoutResult entered.handoff.call gpr rflags)
          completion.event completion.final [] :=
        completion.rawStep completed (Grass.Tests.Win32RawStep.empty_graph_valid _)
          (Grass.Tests.Win32RawStep.empty_graph_valid _) (Raw.Graph.extends_refl [])
      let final : { state : RawState // state.machine.gpr .rax = gpr .rax ∧
          state.machine.rflags = rflags ∧ state.ControlConsistent } :=
        ⟨completion.final, step.stdout_result.1, step.stdout_result.2.1,
          step.stdout_result.2.2.2.2⟩
      let boundary := match completion.event.boundaries with
        | [.returned call caller agent ids] =>
            call == entered.handoff.call && caller == entered.handoff.record.caller &&
              agent == entered.handoff.record.agent && ids == entered.handoff.record.ids
        | _ => false
      let result := match completion.event.kind with
        | .endpoint (.stdoutAcquired call handle) => call == entered.handoff.call && handle == raw
        | _ => false
      some (final.val.machine.gpr .rax == raw && final.val.machine.rflags == rflags &&
        final.val.control == .caller entered.handoff.caller &&
        (final.val.calls.lookup entered.handoff.call).isNone &&
        completion.event.memory.length == 1 && boundary && result)

def regression? : Option Bool :=
  match Grass.Tests.Win32HelloCall.actualHandoff? with
  | none => none
  | some actual => do
    let normal ← regressionFor actual 55 55
    let nullTable ← regressionFor actual 0 0
    let invalid ← regressionFor actual 55 GetStdHandleResult.invalidHandleValue
    pure (normal && nullTable && invalid)

#eval check (regression? == some true)

end Grass.Tests.Win32GetStdHandleRawReturn
