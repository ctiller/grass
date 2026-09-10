import Grass.Platform.Win32.ConsoleEnvironment

/-! Bounded model fixtures for static console attribution.  They make no claim
about the native process table, DLL exports, or concurrent handle lifetime. -/

namespace Grass.Tests.Win32ConsoleEnvironment

open Grass.Core Grass.Std.Logical Grass.Platform.Win32

private def processes : FreshSupply ProcessTag := .initial
private def contexts : FreshSupply ContextTag := .initial
private def routes : FreshSupply RouteTag := .initial
private def generations : FreshSupply GenerationTag := .initial

def process := processes.fresh.1
def caller := contexts.fresh.1
def provider := contexts.fresh.2.fresh.1
def stdout := routes.fresh.1
def otherRoute := routes.fresh.2.fresh.1
def generation := generations.fresh.1
def nextGeneration := generations.fresh.2.fresh.1

def readOnly : HandleBinding :=
  { generation, route := stdout, writable := false, mode := .synchronous }
def wrongRoute : HandleBinding :=
  { generation, route := otherRoute, writable := true, mode := .synchronous }
def overlapped : HandleBinding :=
  { generation, route := stdout, writable := true, mode := .overlapped }
def dummy : HandleBinding :=
  { generation, route := stdout, writable := true, mode := .synchronous }

def bindings : FiniteMap (BitVec 64) HandleBinding :=
  FiniteMap.empty
    |>.insert 55 readOnly
    |>.insert 56 wrongRoute
    |>.insert 57 overlapped
    |>.insert 0 dummy
    |>.insert GetStdHandleResult.invalidHandleValue dummy

def standard : StandardHandles where
  value
    | .input => 0
    | .output => 55
    | .error => GetStdHandleResult.invalidHandleValue

def environment : ConsoleEnvironment :=
  { process, caller, provider, standardHandles := standard, bindings, stdoutRoute := stdout }

def staleStandard : StandardHandles where
  value
    | .input => 58
    | .output => 55
    | .error => GetStdHandleResult.invalidHandleValue

def staleEnvironment : ConsoleEnvironment :=
  { environment with standardHandles := staleStandard }

theorem input_null_table_allowed :
    environment.getStdAllowed StdHandleId.input.value 0 := by decide

theorem output_55_table_allowed :
    environment.getStdAllowed StdHandleId.output.value 55 := by decide

theorem error_invalid_table_allowed :
    environment.getStdAllowed StdHandleId.error.value
      GetStdHandleResult.invalidHandleValue := by decide

/-- A nonsentinel table value remains an allowed raw GetStdHandle result even
when this snapshot has no route attribution for it. -/
theorem stale_unresolved_table_allowed :
    staleEnvironment.getStdAllowed StdHandleId.input.value 58 := by decide

theorem stale_unresolved_has_no_route : staleEnvironment.routeOf? 58 = none := by decide

/-- INVALID_HANDLE_VALUE is an independently permitted failure for every
supported selector; it need not equal that selector's table value. -/
theorem output_independent_invalid_failure :
    environment.getStdAllowed StdHandleId.output.value
      GetStdHandleResult.invalidHandleValue := by decide

theorem different_raw_rejected :
    ¬ environment.getStdAllowed StdHandleId.output.value 56 := by decide

theorem unsupported_selector_rejected : ¬ environment.getStdAllowed 0 55 := by decide

theorem readonly_binding_returned_unchanged : environment.routeOf? 55 = some readOnly := by rfl
theorem wrong_route_binding_returned_unchanged : environment.routeOf? 56 = some wrongRoute := by rfl
theorem overlapped_binding_returned_unchanged : environment.routeOf? 57 = some overlapped := by rfl
theorem missing_binding_refused : environment.routeOf? 58 = none := by decide

/-- Sentinel rejection precedes the map lookup, even when the map contains
dummy entries at both raw values.  This is attribution refusal, not an API
FALSE result. -/
theorem sentinel_bindings_ignored :
    environment.routeOf? 0 = none ∧
      environment.routeOf? GetStdHandleResult.invalidHandleValue = none := by decide

theorem identity_retains_raw_and_generation :
    (readOnly.identity 55).value = 55 ∧
      (readOnly.identity 55).generation = generation := ⟨rfl, rfl⟩

def recycled : HandleBinding := { readOnly with generation := nextGeneration }

theorem same_raw_different_generation_distinct :
    readOnly.identity 55 ≠ recycled.identity 55 := by
  exact Generational.value_eq_insufficient rfl (by decide)

end Grass.Tests.Win32ConsoleEnvironment
