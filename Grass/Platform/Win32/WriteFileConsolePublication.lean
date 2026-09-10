import Grass.Platform.Win32.ConsoleEnvironment
import Grass.Platform.Win32.WriteFileService

/-!
# WriteFile console publication attribution

This leaf classifies an already committed WriteFile publication against a static
console environment.  Refusal is only absence of this attribution scope: it
does not change a WriteFile result, establish native behavior, or infer any
later raw BOOL/result relation.

Writable and synchronous handle applicability follows the bounded profile from
Microsoft's [WriteFile documentation](https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile).
The observation's connection to a native process, fixed physical dispatch and
publication realization, and formal source-ledger anchors remain owed.
-/

namespace Grass.Platform.Win32.WriteFile.ConsolePublication

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState

/-- Concrete data attributed to one committed WriteFile output slice. -/
structure Observation where
  process : ProcessId
  handle : GenerationalBV64
  route : RouteId
  bytes : Vec Byte

/-- Fixed executable attribution against the receipt's own request, caller,
agent, committed output, and the environment's usable-handle lookup. -/
def matches? (environment : ConsoleEnvironment)
    {realization : Realization} {before : RawState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {action : Action} {output : Vec Byte}
    (_receipt : ServiceReceipt realization before call record action output)
    (observation : Observation) : Bool :=
  if observation.process = environment.process then
  if record.caller = environment.caller then
  if record.agent = environment.provider then
  if observation.handle.value = record.request.handle then
    match environment.routeOf? record.request.handle with
    | none => false
    | some binding =>
        binding.generation == observation.handle.generation &&
        binding.route == observation.route &&
        binding.writable && binding.mode == .synchronous &&
        observation.bytes == output
  else false else false else false else false

/-- Compare the observation route with the selected stdout route. Publication
attribution additionally requires `matches?`, as checked by `extendConsole?`. -/
def onStdout (environment : ConsoleEnvironment) (observation : Observation) : Bool :=
  observation.route == environment.stdoutRoute

theorem matched_bytes {environment : ConsoleEnvironment}
    {realization : Realization} {before : RawState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {action : Action} {output : Vec Byte}
    {receipt : ServiceReceipt realization before call record action output}
    {observation : Observation}
    (matched : matches? environment receipt observation = true) : observation.bytes = output := by
  unfold matches? at matched
  repeat' split at matched <;> try contradiction
  simp_all

theorem matched_target {environment : ConsoleEnvironment}
    {realization : Realization} {before : RawState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {action : Action} {output : Vec Byte}
    {receipt : ServiceReceipt realization before call record action output}
    {observation : Observation}
    (matched : matches? environment receipt observation = true) :
    observation.process = environment.process ∧
      record.caller = environment.caller ∧ record.agent = environment.provider ∧
      observation.handle.value = record.request.handle ∧ observation.bytes = output ∧
      ∃ binding, environment.routeOf? record.request.handle = some binding ∧
        binding.generation = observation.handle.generation ∧ binding.route = observation.route ∧
        binding.writable = true ∧ binding.mode = .synchronous := by
  unfold matches? at matched
  repeat' split at matched <;> try contradiction
  simp_all

@[simp] theorem onStdout_eq_true_iff (environment : ConsoleEnvironment) (observation : Observation) :
    onStdout environment observation = true ↔ observation.route = environment.stdoutRoute := by
  simp [onStdout]

/-- The committed receipt retains the exact provider publication suffix. -/
theorem publication_suffix {realization : Realization} {before : RawState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {action : Action} {output : Vec Byte}
    (receipt : ServiceReceipt realization before call record action output) :
    output = (record.request.bytes.drop receipt.pre.accepted).take
      (receipt.post.accepted - receipt.pre.accepted) :=
  receipt.committed.publication.suffix

/-- The committed output extends exactly the receipt's existing publication
frontier; no separate output list is accepted by this attribution layer. -/
theorem publication_prefix {realization : Realization} {before : RawState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {action : Action} {output : Vec Byte}
    (receipt : ServiceReceipt realization before call record action output) :
    receipt.pre.output ++ output = receipt.post.output :=
  receipt.committed.publication.append_prefix

end Grass.Platform.Win32.WriteFile.ConsolePublication
