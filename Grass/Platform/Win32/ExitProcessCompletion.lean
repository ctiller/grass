import Grass.Platform.Win32.ConsoleEnvironment
import Grass.Platform.Win32.ExitProcessRuntime

/-!
# Completed ExitProcess observation

This module checks a finite environment observation against the exact pending
`ExitProcess` occurrence.  Completion changes only the control marker.  The
machine, protocol metadata, runtime table, and their logs remain an inert
archive; no ABI return, resource reclamation, obligation discharge, or native
responsiveness is inferred here.
-/

namespace Grass.Platform.Win32.ExitProcess

open Grass.Core Grass.Op
open Grass.Platform.Win32.ExecutionState

/-- Data supplied by the fixed console environment when it observes process
completion.  Native applicability is the external profile's responsibility. -/
structure Observation where
  process : ProcessId
  call : CallProtocol.CallId
  status : BitVec 32
deriving DecidableEq, Repr

/-- Evidence that one observation names the exact pending terminal call. -/
structure Completion (environment : ConsoleEnvironment) (before : RawState)
    (observed : Observation) where
  processExact : observed.process = environment.process
  controlExact : before.control =
    .pending observed.call environment.caller environment.provider
  runtimeExact : before.calls.lookup observed.call = some .exitProcess
  pending : CallProtocol.Pending ApiRequest
  pendingExact : before.metadata.pending.lookup observed.call = some pending
  callerExact : pending.caller = environment.caller
  providerExact : pending.agent = environment.provider
  requestExact : pending.request = .exitProcess observed.status

/-- Check the complete finite observation against the archived pending state.
No field is changed when a check refuses. -/
def complete? (environment : ConsoleEnvironment) (before : RawState)
    (observed : Observation) : Option (Completion environment before observed) :=
  if processExact : observed.process = environment.process then
  if controlExact : before.control =
      .pending observed.call environment.caller environment.provider then
    match runtimeExact : before.calls.lookup observed.call with
    | some .exitProcess =>
        match pendingExact : before.metadata.pending.lookup observed.call with
        | none => none
        | some pending =>
            if callerExact : pending.caller = environment.caller then
            if providerExact : pending.agent = environment.provider then
              match requestExact : pending.request with
              | .exitProcess status =>
                  if statusExact : status = observed.status then
                    some {
                      processExact := processExact
                      controlExact := controlExact
                      runtimeExact := runtimeExact
                      pending := pending
                      pendingExact := pendingExact
                      callerExact := callerExact
                      providerExact := providerExact
                      requestExact := by rw [requestExact, statusExact] }
                  else none
              | .getStdHandle _ | .writeFile _ => none
            else none else none
    | none | some (.getStdHandle _) | some (.writeFile _) => none
  else none else none

namespace Completion

/-- The archival terminal snapshot.  No field other than control changes. -/
def after {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (_completion : Completion environment before observed) : RawState :=
  { before with control := .terminal observed.call observed.status }

@[simp] theorem control {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (completion : Completion environment before observed) :
    completion.after.control = .terminal observed.call observed.status := rfl

@[simp] theorem machine {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (completion : Completion environment before observed) :
    completion.after.machine = before.machine := rfl

@[simp] theorem metadata {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (completion : Completion environment before observed) :
    completion.after.metadata = before.metadata := rfl

@[simp] theorem calls {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (completion : Completion environment before observed) :
    completion.after.calls = before.calls := rfl

theorem pending_archived {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (completion : Completion environment before observed) :
    completion.after.metadata.pending.lookup observed.call = some completion.pending := by
  rw [completion.metadata]
  exact completion.pendingExact

theorem runtime_archived {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (completion : Completion environment before observed) :
    completion.after.calls.lookup observed.call = some .exitProcess := by
  rw [completion.calls]
  exact completion.runtimeExact

theorem observed_status_exact {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (completion : Completion environment before observed) :
    completion.pending.request = .exitProcess observed.status :=
  completion.requestExact

theorem observed_process_exact {environment : ConsoleEnvironment} {before : RawState}
    {observed : Observation} (completion : Completion environment before observed) :
    observed.process = environment.process :=
  completion.processExact

end Completion
end Grass.Platform.Win32.ExitProcess
