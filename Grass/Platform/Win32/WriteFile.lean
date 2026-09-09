import Grass.Platform.Win32.ApiRequest
import Grass.Platform.Win32.WriteFileCallPlan
import Grass.Op.CallProtocolCustody
import Grass.Std.Logical.Vec

variable {plan : Grass.Platform.Win32.WriteFile.LoanPlan}

/-!
# Evidence for a synchronous WriteFile provider prefix

Microsoft WriteFile, Parameters and Synchronous Handles, retrieved 2026-09-09:
https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile

This is a consumer of execution evidence, not an executable Windows provider.
The initial spatial profile uses placed, nonwrapping allocations with dedicated backing storage.
Physical action dispatch, ordering and provider-accepted output require external
realization witnesses. The generic step takes an agent identity, not a call ID:
its success does not establish which pending occurrence caused that action.
Neither successful bookkeeping nor these witnesses prove eventual return.
-/
namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

/-- Exact pending occurrence; loan identities stay in the record, not recomputed.
Applicability of the synchronous handle and its ABI arguments remains separate. -/
structure PendingAt (plan : LoanPlan) (state : ProtocolState) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) : Prop where
  lookup : state.pending.lookup call = some (embedPending record)
  custody : record.Valid state.machine.memory
  loans : record.LoanPartition record.request.loans plan.additional

/-- Incremental accepted output, distinct from a reported DWORD or device durability. -/
structure Publication (bytes : Vec Byte) (before after : Nat) (output : Vec Byte) : Prop where
  monotone : before ≤ after
  bounded : after ≤ bytes.length
  suffix : output = (bytes.drop before).take (after - before)

theorem Publication.append_prefix {bytes output : Vec Byte} {before after : Nat}
    (publication : Publication bytes before after output) :
    bytes.take before ++ output = bytes.take after := by
  rw [publication.suffix, ← Vec.take_add]
  have h := publication.monotone
  congr 1
  omega

/-- `Publication.output_unique` fixes the output at a chosen pair of endpoints. -/
theorem Publication.output_unique {bytes left right : Vec Byte} {before after : Nat}
    (a : Publication bytes before after left) (b : Publication bytes before after right) :
    left = right := a.suffix.trans b.suffix.symm

structure Prefix (plan : LoanPlan) (state : ProtocolState) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) where
  pending : PendingAt plan state call record
  prepared : Prepared state.machine.memory record.request
  clean : state.machine.violations.IsEmpty
  accepted : Nat
  bounded : accepted ≤ record.request.bytes.length

def Prefix.output {state : ProtocolState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} (frontier : Prefix plan state call record) : Vec Byte :=
  record.request.bytes.take frontier.accepted

/-- A concrete provider memory action. Its identity and fault plan are retained. -/
structure Action where
  policy : StepPolicy
  operation : SomeOperation
  kind : ContextKind
  cause : EventCause
  faultAt : (sequence : SubstepSequence) → FaultPlan sequence

def Action.Runs (action : Action) (record : CallProtocol.Pending Request)
    (before after : ProtocolState) : Prop :=
  CallProtocol.step? before action.policy action.operation record.agent action.kind
    action.cause action.faultAt = some after

inductive CausalNode where
  | entry (call : CallProtocol.CallId)
  | returned (call : CallProtocol.CallId)
  | event (id : EventId)
deriving DecidableEq

def Represented (state : ProtocolState) : CausalNode → Prop
  | .entry call => ∃ caller agent loans,
      CallProtocol.Boundary.handoff call caller agent loans ∈ state.boundaries
  | .returned call => ∃ caller agent loans,
      CallProtocol.Boundary.returned call caller agent loans ∈ state.boundaries
  | .event id => ∃ event ∈ state.machine.events, event.event.id = id

/-- Select once outside a whole prefix derivation. No default relation is supplied. -/
structure CausalModel where
  precedes : ProtocolState → CausalNode → CausalNode → Prop

structure CausalModel.Valid (model : CausalModel) (state : ProtocolState) : Prop where
  endpoints : ∀ a b, model.precedes state a b → Represented state a ∧ Represented state b
  irreflexive : ∀ node, ¬ model.precedes state node node
  transitive : ∀ a b c, model.precedes state a b → model.precedes state b c →
    model.precedes state a c

structure HandoffCausality (model : CausalModel) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) (before after : ProtocolState) : Prop where
  beforeValid : model.Valid before
  afterValid : model.Valid after
  historyExtends : ∀ a b, model.precedes before a b → model.precedes after a b
  entry : CallProtocol.Boundary.handoff call record.caller record.agent record.ids ∈ after.boundaries
  callerEntry : ∀ old ∈ before.machine.events, old.event.context.id = record.caller →
    model.precedes after (.event old.event.id) (.entry call)

/-- Fixed graph obligations, including actual matched entry and exact new events.
Pending-prefix steps do not themselves establish a return edge.
Integrating these premises with `Grass.Op.step` is an open obligation. -/
structure CausalEvidence (plan : LoanPlan) (model : CausalModel) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) (action : Action)
    (before after : ProtocolState) (added : List ValidMemoryEvent) : Prop where
  entry : CallProtocol.Boundary.handoff call record.caller record.agent record.ids ∈
    before.boundaries
  events : after.machine.events = before.machine.events ++ added
  fresh : ∀ event ∈ added, ∀ old ∈ before.machine.events, event.event.id ≠ old.event.id
  beforeValid : model.Valid before
  afterValid : model.Valid after
  historyExtends : ∀ a b, model.precedes before a b → model.precedes after a b
  callerEntry : ∀ old ∈ before.machine.events, old.event.context.id = record.caller →
    model.precedes after (.event old.event.id) (.entry call)
  entryEffects : ∀ event ∈ added, event.event.context.id = record.agent ∧
    model.precedes after (.entry call) (.event event.event.id)
  footprint : ∀ event ∈ added,
    (event.event.kind.reads = true →
      plan.ReadFootprint record.request event.event.provenance event.event.range) ∧
    (event.event.kind.writes = true →
      plan.WriteFootprint record.request event.event.provenance event.event.range)
  conflicts : ∀ old ∈ before.machine.events, ∀ event ∈ added,
    old.event.context.id ≠ event.event.context.id →
    MemoryEvent.Conflicts (fun a b => action.policy.compatible a b = true)
      old.event event.event →
    model.precedes after (.event old.event.id) (.event event.event.id)

/-- Observation remains an explicit external realization obligation indexed by
the exact occurrence, action, worlds, counts and bytes; no default is supplied. -/
structure Realization where
  causal : CausalModel
  /-- `Realization.executesFor` is an open physical-dispatch obligation,
  including when an agent serves multiple calls. -/
  executesFor : CallProtocol.CallId → CallProtocol.Pending Request → Action →
    ProtocolState → ProtocolState → Prop
  publishes : CallProtocol.CallId → CallProtocol.Pending Request → Action →
    ProtocolState → ProtocolState → Nat → Nat → Vec Byte → Prop

/-- Only count-slot bytes and the fixed plan's writable additional footprint
may change in this bounded provider slice. -/
def Confined (plan : LoanPlan) (request : Request) (before after : MemoryState) : Prop :=
  ∀ root offset,
    ¬ plan.WriteAt request root offset →
    after.cellAt? root offset = before.cellAt? root offset

structure CommittedStep (realization : Realization)
    {before after : ProtocolState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request}
    (pre : Prefix plan before call record) (post : Prefix plan after call record)
    (action : Action) (output : Vec Byte) : Prop where
  ran : action.Runs record before after
  dispatch : realization.executesFor call record action before after
  publishes : realization.publishes call record action before after
    pre.accepted post.accepted output
  publication : Publication record.request.bytes pre.accepted post.accepted output
  obligations : after.machine.obligations = before.machine.obligations
  metadata : ∀ root, (after.machine.memory.allocations.lookup root).map AllocationRecord.metadata =
    (before.machine.memory.allocations.lookup root).map AllocationRecord.metadata
  confined : Confined plan record.request before.machine.memory after.machine.memory
  causal : ∃ added, CausalEvidence plan realization.causal call record action before after added

theorem CommittedStep.output_extends {realization : Realization}
    {before after : ProtocolState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request}
    {pre : Prefix plan before call record} {post : Prefix plan after call record}
    {action : Action} {output : Vec Byte}
    (step : CommittedStep realization pre post action output) :
    pre.output ++ output = post.output := step.publication.append_prefix

theorem Prefix.no_denial {state : ProtocolState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} (frontier : Prefix plan state call record) :
    state.machine.violations.records? = [] :=
  (AuditViolationLedger.isEmpty_iff_records?_nil _).mp frontier.clean

theorem PendingAt.same_record {state : ProtocolState} {call : CallProtocol.CallId}
    {left right : CallProtocol.Pending Request}
    (a : PendingAt plan state call left) (b : PendingAt plan state call right) : left = right := by
  exact embedPending_injective (Option.some.inj (a.lookup.symm.trans b.lookup))

/-- Reachable evidence starts at the actual handoff with zero accepted bytes.
The outer realization is fixed across the entire derivation. An arbitrary
`Prefix` alone must never be advertised as a reachable provider history. -/
inductive History (plan : LoanPlan) (realization : Realization) (initial : ProtocolState)
    (call : CallProtocol.CallId) (record : CallProtocol.Pending Request) :
    {state : ProtocolState} → Prefix plan state call record → Type 1 where
  | handoff {state : ProtocolState} (frontier : Prefix plan state call record)
      (ran : CallProtocol.handoff? initial record.caller record.agent (.writeFile record.request)
        (plan.requests record.request) = some (call, state))
      (input : Prepared initial.machine.memory record.request)
      (causal : HandoffCausality realization.causal call record initial state)
      (zero : frontier.accepted = 0) : History plan realization initial call record frontier
  | step {before after : ProtocolState}
      {pre : Prefix plan before call record} {post : Prefix plan after call record}
      (history : History plan realization initial call record pre)
      (action : Action) (output : Vec Byte)
      (committed : CommittedStep realization pre post action output) :
      History plan realization initial call record post

def History.published {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    (history : History plan realization initial call record frontier) : Vec Byte :=
  match history with
  | .handoff .. => .fromList []
  | .step previous _ output _ => previous.published ++ output

/-- Every finite derived history publishes exactly its cumulative request prefix,
not merely some bounded collection of bytes. -/
theorem History.published_eq_output {realization : Realization}
    {initial : ProtocolState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {state : ProtocolState}
    {frontier : Prefix plan state call record}
    (history : History plan realization initial call record frontier) :
    history.published = frontier.output := by
  induction history with
  | handoff frontier _ _ _ zero => simp [History.published, Prefix.output, zero, Vec.empty]
  | step previous action output committed ih =>
    change previous.published ++ output = _
    rw [ih]
    exact committed.output_extends

theorem History.causal_valid {realization : Realization}
    {initial : ProtocolState} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {state : ProtocolState}
    {frontier : Prefix plan state call record}
    (history : History plan realization initial call record frontier) : realization.causal.Valid state := by
  cases history with
  | handoff _ _ _ causal _ => exact causal.afterValid
  | step _ _ _ committed => obtain ⟨_, causal⟩ := committed.causal; exact causal.afterValid

end Grass.Platform.Win32.WriteFile
