import Grass.Platform.Win32.GetStdHandleReturn
import Tests.Platform.Win32HelloCall

/-!
# Actual Hello GetStdHandle return fixture

This model fixture retains the actual evaluated CALL and checked handoff from
`Win32HelloCall`.  The supplied provider registers remain observations: no
native provider execution, export adequacy, or repaired register state is
claimed here.
-/

namespace Grass.Tests.Win32GetStdHandleReturn

open Grass.Core Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader
open Grass.Op

private def processes : FreshSupply ProcessTag := .initial
private def routes : FreshSupply RouteTag := .initial

def environmentFor (caller provider : ContextId) (tableRaw : BitVec 64) : ConsoleEnvironment :=
  { process := processes.fresh.1
    caller, provider
    standardHandles := { value := fun
      | .input => 0
      | .output => tableRaw
      | .error => GetStdHandleResult.invalidHandleValue }
    bindings := .empty
    stdoutRoute := routes.fresh.1 }

private def check (label : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError ("GetStdHandle return fixture failed: " ++ label))

def evaluatedFor {setup : Grass.Tests.Win32HelloCall.ActualSetup}
    (handoff : Grass.Tests.Win32HelloCall.ActualHandoff setup) :
    Raw.EvaluatedCall setup.loaded handoff.entered.checked handoff.entered.receipt := by
  cases handoff with
  | mk pre policy selected flags called evaluated raw receiptExact =>
      cases raw with
      | mk checked checkedExact receipt entered =>
          have same : checked = pre.checked :=
            Option.some.inj (checkedExact.symm.trans pre.checkedExact)
          cases same
          exact
            { policy := policy
              selected := selected
              flags := flags
              success := called
              evaluated := evaluated
              receiptExact := receiptExact.symm }

def regressionFor (actual : Grass.Tests.Win32HelloCall.ActualResult) : Option Bool := do
  let setup : Grass.Tests.Win32HelloCall.ActualSetup := actual.setup
  let handoff : Grass.Tests.Win32HelloCall.ActualHandoff setup := actual.handoff
  let entered := handoff.entered.entered
  let prior := handoff.preCall.before.calls
  let evaluated := evaluatedFor handoff
  let environment (tableRaw : BitVec 64) :=
    environmentFor entered.handoff.caller setup.inputs.independentContext tableRaw
  let gpr (raw : BitVec 64) : Gpr → BitVec 64 := fun register =>
    if register = .rax then raw else entered.reached.machine.gpr register
  let observe (tableRaw raw : BitVec 64) :=
    GetStdHandle.ProviderResult.observe? setup.loaded (environment tableRaw)
      entered evaluated prior (gpr raw) entered.reached.machine.rflags
  let completeOne (tableRaw raw : BitVec 64) : Option Bool := do
    let observed ← (observe tableRaw raw).toOption
    match (GetStdHandle.Return.complete? observed).toOption with
    | none => none
    | some completion => do
      let checked ← completion.final.checked?
      let returnedProtocol ← checked.callProtocol?
      pure (completion.final.machine.gpr .rax == raw &&
        (completion.final.calls.lookup entered.handoff.call).isNone &&
        completion.final.control == ExecutionState.Control.caller entered.handoff.caller &&
        (checked.metadata.pending.lookup entered.handoff.call).isNone &&
        (CallProtocol.return? returnedProtocol entered.handoff.call
          entered.handoff.record.caller entered.handoff.record.agent
          entered.handoff.record.ids).isNone)
  let some raw55 := completeOne 55 55 | none
  let some nullTable := completeOne 0 0 | none
  let some invalidTable := completeOne GetStdHandleResult.invalidHandleValue
    GetStdHandleResult.invalidHandleValue | none
  let some independentInvalid := completeOne 55 GetStdHandleResult.invalidHandleValue | none
  let mismatchedRaw := match observe 55 56 with
    | .error .handle => true | _ => false
  let wrongRspGpr : Gpr → BitVec 64 := fun register =>
    if register = .rsp then entered.reached.machine.gpr .rsp + 8
    else if register = .rax then 55 else entered.reached.machine.gpr register
  let wrongRsp := match GetStdHandle.ProviderResult.observe? setup.loaded (environment 55)
      entered evaluated prior wrongRspGpr entered.reached.machine.rflags with
    | .error .rsp => true | _ => false
  let wrongRbxGpr : Gpr → BitVec 64 := fun register =>
    if register = .rbx then entered.reached.machine.gpr .rbx + 1
    else if register = .rax then 55 else entered.reached.machine.gpr register
  let wrongRbx := match GetStdHandle.ProviderResult.observe? setup.loaded (environment 55)
      entered evaluated prior wrongRbxGpr entered.reached.machine.rflags with
    | .error .nonvolatile => true | _ => false
  some (raw55 && nullTable && invalidTable && independentInvalid && mismatchedRaw && wrongRsp && wrongRbx &&
    wrongRspGpr .rsp == entered.reached.machine.gpr .rsp + 8 &&
    wrongRbxGpr .rbx == entered.reached.machine.gpr .rbx + 1)

def regression? : Option Bool :=
  Grass.Tests.Win32HelloCall.actualHandoff?.bind regressionFor

#eval check "actual observed returns and refusals" (regression? == some true)

end Grass.Tests.Win32GetStdHandleReturn
