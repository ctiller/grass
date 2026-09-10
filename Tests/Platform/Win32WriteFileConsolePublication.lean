import Grass.Platform.Win32.WriteFileConsolePublication
import Tests.Platform.Win32WriteFileService

/-! Static attribution tests over the existing conditional quiet service
receipt.  That receipt has a real committed model step and zero-byte output,
but it is not evidence of native WriteFile execution or a reached history. -/

namespace Grass.Tests.Win32WriteFileConsolePublication

open Grass.Core Grass.Std.Logical Grass.Platform.Win32
open Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.WriteFile.ConsolePublication

private def processes : FreshSupply ProcessTag := .initial
private def routes : FreshSupply RouteTag := .initial
private def generations : FreshSupply GenerationTag := .initial

def process := processes.fresh.1
def otherProcess := processes.fresh.2.fresh.1
def stdout := routes.fresh.1
def otherRoute := routes.fresh.2.fresh.1
def generation := generations.fresh.1
def otherGeneration := generations.fresh.2.fresh.1

def binding : HandleBinding :=
  { generation, route := stdout, writable := true, mode := .synchronous }

def environment : ConsoleEnvironment :=
  { process
    caller := Grass.Tests.Spike1.mainThread
    provider := Grass.Tests.Spike1.apiAgent
    standardHandles := { value := fun _ => 123 }
    bindings := FiniteMap.empty.insert 123 binding
    stdoutRoute := stdout }

def observation : Observation :=
  { process, handle := binding.identity 123, route := stdout, bytes := .empty }

abbrev receipt := Grass.Tests.Win32WriteFileService.receipt₁

private def check (label : String) (passed : Bool) : IO Unit :=
  unless passed do
    throw (IO.userError ("WriteFile console publication fixture failed: " ++ label))

#eval check "exact attribution" (matches? environment receipt observation == true)
theorem exact_quiet_publication_is_stdout : onStdout environment observation = true := by decide

#eval check "different process rejected"
  (matches? environment receipt { observation with process := otherProcess } == false)

def wrongCallerEnvironment : ConsoleEnvironment :=
  { environment with caller := Grass.Tests.Spike1.apiAgent }

#eval check "different caller rejected"
  (matches? wrongCallerEnvironment receipt observation == false)

def wrongProviderEnvironment : ConsoleEnvironment :=
  { environment with provider := Grass.Tests.Spike1.mainThread }

#eval check "different provider rejected"
  (matches? wrongProviderEnvironment receipt observation == false)

#eval check "different generation rejected" (matches? environment receipt
  { observation with handle := ⟨123, otherGeneration⟩ } == false)

#eval check "different raw handle rejected" (matches? environment receipt
  { observation with handle := binding.identity 124 } == false)

#eval check "different output rejected" (matches? environment receipt
  { observation with bytes := .fromList [11] } == false)

#eval check "different observation route rejected" (matches? environment receipt
  { observation with route := otherRoute } == false)

def readOnlyEnvironment : ConsoleEnvironment :=
  { environment with bindings := FiniteMap.empty.insert 123 { binding with writable := false } }

#eval check "readonly binding rejected"
  (matches? readOnlyEnvironment receipt observation == false)

def overlappedEnvironment : ConsoleEnvironment :=
  { environment with bindings := FiniteMap.empty.insert 123 { binding with mode := .overlapped } }

#eval check "overlapped binding rejected"
  (matches? overlappedEnvironment receipt observation == false)

def unresolvedEnvironment : ConsoleEnvironment := { environment with bindings := .empty }

#eval check "unresolved handle rejected"
  (matches? unresolvedEnvironment receipt observation == false)

/-- General publication attribution preserves the environment's actual route.
A matching non-stdout route is valid attribution while `onStdout` remains false. -/
def otherBinding : HandleBinding := { binding with route := otherRoute }
def otherRouteEnvironment : ConsoleEnvironment :=
  { environment with bindings := FiniteMap.empty.insert 123 otherBinding }
def otherRouteObservation : Observation :=
  { observation with handle := otherBinding.identity 123, route := otherRoute }

#eval check "matching non-stdout route attributed"
  (matches? otherRouteEnvironment receipt otherRouteObservation == true)
theorem matching_wrong_route_is_not_stdout :
    onStdout otherRouteEnvironment otherRouteObservation = false := by decide

/-- Exact output follows the committed frontier law.  Attribution refusal does
not manufacture an API FALSE result; this leaf carries no BOOL observation. -/
theorem quiet_output_is_actual_zero_suffix :
    (Grass.Tests.Win32WriteFileService.record.request.bytes.drop
      receipt.pre.accepted).take (receipt.post.accepted - receipt.pre.accepted) = .empty := by
  rw [← publication_suffix receipt]
  rfl

end Grass.Tests.Win32WriteFileConsolePublication
