import Grass.Platform.Win32.ExitProcessRawCompletion
import Tests.Platform.Win32RawStep
import Tests.Platform.Win32ExitProcessRuntime
import Tests.Platform.Win32WriteFileService
import Tests.Platform.Win32ConsoleEnvironment

/-!
# ExitProcess completion model regression

This finite model checks archival of an already pending ExitProcess occurrence.
It does not claim native process termination or responsiveness.
-/

namespace Grass.Tests.Win32ExitProcessCompletion

open Grass.Core Grass.Std.Logical Grass.Platform.Win32
open Grass.Platform.Win32.ExecutionState Grass.Tests.Spike1

private def cpu : Grass.ISA.X86.Execution.State :=
  { machine := Grass.Tests.Win32ApiRequest.afterStd.machine.noteContext apiAgent .externalAgent
    gpr := fun register => if register = .rcx then 0x1234567800000001 else 0
    rip := 0, rflags := 0 }

private def entryBefore : State ApiRequest :=
  { machine := cpu, metadata := Grass.Tests.Win32ApiRequest.afterStd.metadata
    control := .caller mainThread, protocolValid := by decide }

private def handoff := (ExitProcess.entryHandoff? entryBefore apiAgent).get (by decide)

/-- The base table is deliberately nonempty, and the protocol already contains
the unrelated GetStdHandle occurrence from `afterStd`. -/
private def baseCalls : CallRuntimeTable :=
  FiniteMap.empty.insert Grass.Tests.Win32ApiRequest.stdCall
    (.getStdHandle Grass.Tests.Win32WriteFileService.runtime.toReturnFrame)

def before : RawState := handoff.initRaw baseCalls

def environment : ConsoleEnvironment :=
  Grass.Tests.Win32ConsoleEnvironment.environment

def observed : ExitProcess.Observation :=
  { process := environment.process, call := handoff.call, status := 1 }

private def processSupply : FreshSupply ProcessTag := .initial
def otherProcess : ProcessId := processSupply.fresh.2.fresh.1

private def check (label : String) (passed : Bool) : IO Unit :=
  unless passed do
    throw (IO.userError ("ExitProcess completion fixture failed: " ++ label))

def completion? := ExitProcess.complete? environment before observed

#eval check "exact pending exit accepted" completion?.isSome

def completion := completion?.get (by decide)

#eval check "terminal snapshot refuses replay"
  (ExitProcess.complete? environment completion.after observed).isNone

theorem success_archives_exact_data :
    completion.after.control = .terminal observed.call observed.status ∧
      completion.after.machine = before.machine ∧
      completion.after.metadata = before.metadata ∧
      completion.after.calls = before.calls ∧
      completion.after.metadata.pending.lookup observed.call = some completion.pending ∧
      completion.after.calls.lookup observed.call = some .exitProcess := by
  exact ⟨completion.control, completion.machine, completion.metadata, completion.calls,
    completion.pending_archived, completion.runtime_archived⟩

theorem unrelated_pending_and_runtime_are_archived :
      completion.after.metadata.pending.lookup Grass.Tests.Win32ApiRequest.stdCall =
        before.metadata.pending.lookup Grass.Tests.Win32ApiRequest.stdCall ∧
      completion.after.calls.lookup Grass.Tests.Win32ApiRequest.stdCall =
        some (.getStdHandle Grass.Tests.Win32WriteFileService.runtime.toReturnFrame) := by
  exact ⟨congrArg (fun metadata => metadata.pending.lookup
      Grass.Tests.Win32ApiRequest.stdCall) completion.metadata, rfl⟩

#eval check "wrong process refused"
  (ExitProcess.complete? environment before
    { observed with process := otherProcess }).isNone

#eval check "wrong call refused"
  (ExitProcess.complete? environment before
    { observed with call := Grass.Tests.Win32ApiRequest.stdCall }).isNone

#eval check "wrong status refused"
  (ExitProcess.complete? environment before { observed with status := 2 }).isNone

def callerControl : RawState := { before with control := .caller environment.caller }

#eval check "wrong control refused"
  (ExitProcess.complete? environment callerControl observed).isNone

def missingRuntime : RawState := { before with calls := .empty }

#eval check "missing runtime refused"
  (ExitProcess.complete? environment missingRuntime observed).isNone

def wrongRuntimeKind : RawState :=
  { before with calls := (before.calls.insert handoff.call
      (CallRuntime.writeFile Grass.Tests.Win32WriteFileService.runtime)) }

#eval check "wrong runtime kind refused"
  (ExitProcess.complete? environment wrongRuntimeKind observed).isNone

/-- The checked completion installs the exact terminal edge for every fixed
interpretation. Empty graphs discharge only the bounded graph obligations. -/
theorem raw_edge {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    (loaded : Loader.LoadedImage image inputs) (realization : WriteFile.Realization)
    (interpretation : WriteFile.ReturnInterpretation) :
    Raw.RawStep loaded realization environment interpretation [] before
      (.exitObservation observed.call observed.status) completion.event completion.after [] :=
  completion.rawStep rfl (Grass.Tests.Win32RawStep.empty_graph_valid _) (Grass.Tests.Win32RawStep.empty_graph_valid _)
    (Raw.Graph.extends_refl [])

theorem raw_edge_retains_terminal_archive
    {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    (loaded : Loader.LoadedImage image inputs) (realization : WriteFile.Realization)
    (interpretation : WriteFile.ReturnInterpretation) :
    completion.after.control = .terminal observed.call observed.status ∧
      completion.after.machine = before.machine ∧
      completion.after.metadata = before.metadata ∧
      completion.after.calls = before.calls ∧
      completion.event.kind = .endpoint (.processExited observed.call observed.status) ∧
      ∃ pending, completion.after.metadata.pending.lookup observed.call = some pending ∧
        pending.request = .exitProcess observed.status :=
  (raw_edge loaded realization interpretation).exit_result

/-- Terminal control excludes every later raw choice, independent of archived
pending/runtime inventory. -/
theorem terminal_has_no_future
    {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {realization : WriteFile.Realization}
    {interpretation : WriteFile.ReturnInterpretation} {graph nextGraph : Raw.Graph}
    {choice : Raw.Choice} {event : Raw.Event} {after : RawState} :
    ¬ Raw.RawStep loaded realization environment interpretation graph completion.after
      choice event after nextGraph :=
  Raw.RawStep.terminal_no_step completion.control

end Grass.Tests.Win32ExitProcessCompletion
