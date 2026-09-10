import Grass.Platform.Win32.ConsoleEnvironment
import Grass.Platform.Win32.WriteFileReturn

/-!
# Selected Win32 provider contract

This leaf defines the response vocabulary and allowed-response projection for
one actual pending Win32 call.  Consumers retain the computed PE import binding,
the exact call record, and the environment's caller/provider identities directly.

`ApiDispatch.Binding` establishes logical applicability to the materialized
import.  Native DLL/export adequacy remains outside that type and outside this
module.  No nonresponse permission, raw waiting boundary, response path, or
completed program is constructed here.  In particular, there is no default
`AllowsPermanentWait`: that requires an authoritative provider-owned selector.
The `ExitProcess` carrier indexes terminal settlement only.  Its consumer must
start from active pending control and prove the same-call, same-status
`exitObservation` and actual completed-exit path.  The carrier implies no ABI
return, fallthrough, record deletion, resource release, or responsiveness.
-/

namespace Grass.Platform.Win32.ProviderContract

open Grass.Core Grass.Op

/-- The endpoint settlement selected by an installed raw choice.  `Unit` for
ExitProcess carries no fabricated return value: a consumer must still prove the
actual `exitObservation` terminal edge for the request's status. -/
def ApiResponse : ApiRequest → Type
  | .getStdHandle _ => BitVec 64
  | .writeFile _ => WriteFile.ReturnResult
  | .exitProcess _ => Unit

/-- An allowed WriteFile result projects an actual matched return for this same
call and selected pending record.  `MatchedReturn.conforms` retains the existing
memory/count observation; no second BOOL rule is introduced here. -/
def WriteFileAllowed (interpretation : WriteFile.ReturnInterpretation)
    (call : CallProtocol.CallId) (record : CallProtocol.Pending ApiRequest)
    (result : WriteFile.ReturnResult) : Prop :=
  ∃ (request : WriteFile.Request) (writeRecord : CallProtocol.Pending WriteFile.Request),
    record.request = .writeFile request ∧
    WriteFile.selectPending record = some writeRecord ∧
    ∃ (plan : WriteFile.LoanPlan) (realization : WriteFile.Realization)
      (initial before after : WriteFile.ProtocolState)
      (frontier : WriteFile.Prefix plan before call writeRecord)
      (history : WriteFile.History plan realization initial call writeRecord frontier),
      WriteFile.MatchedReturn interpretation history result after

/-- Fixed allowance for the selected pending record.  A request with a
different payload has no response under this occurrence's contract. -/
def Allowed (environment : ConsoleEnvironment)
    (interpretation : WriteFile.ReturnInterpretation)
    (call : CallProtocol.CallId) (record : CallProtocol.Pending ApiRequest) :
    (request : ApiRequest) → ApiResponse request → Prop
  | .getStdHandle selector, handle =>
      record.request = .getStdHandle selector ∧ environment.getStdAllowed selector handle
  | .writeFile request, result =>
      record.request = .writeFile request ∧ WriteFileAllowed interpretation call record result
  -- Unit identifies the sole response shape; it does not witness a terminal edge.
  | .exitProcess status, () => record.request = .exitProcess status

end Grass.Platform.Win32.ProviderContract
