import Grass.Op.CallProtocol
import Grass.Std.Logical.Vec

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

structure Argument where
  provenance : Provenance
  range : ByteRange
deriving DecidableEq, Repr

/-- Resolve against the actual live allocation, retaining the lookup and placement.
This supplies spatial evidence only, never access rights. -/
structure Resolved (memory : MemoryState) (arg : Argument)
    extends memory.ResolvedAccess arg.provenance arg.range where
  base : MachineAddress
  placed : allocation.base = some base
  noWrap : FitsAllocation base allocation.extent.stop

def Resolved.physical {memory : MemoryState} {arg : Argument}
    (resolved : Resolved memory arg) : ByteRange :=
  arg.range.shift resolved.base.toNat

theorem Resolved.root_contains {memory : MemoryState} {arg : Argument}
    (resolved : Resolved memory arg) : resolved.allocation.extent.Contains arg.range := by
  rw [resolved.extentAgrees]
  exact (Provenance.extent_within_root resolved.provenanceNested).trans resolved.rangeInProvenance

def Resolved.transport {before after : MemoryState} {arg : Argument}
    (resolved : Resolved before arg) (same : after.allocations = before.allocations)
    (backings : after.backings = before.backings) : Resolved after arg :=
  { toResolvedAccess := resolved.toResolvedAccess.transport same backings
    base := resolved.base, placed := resolved.placed, noWrap := resolved.noWrap }

structure Request where
  handle : BitVec 64
  requested : BitVec 32
  buffer : Argument
  countSlot : Argument
  bytes : Vec Byte

def Request.loans (request : Request) : List CallProtocol.LoanRequest :=
  [⟨.loan, request.buffer.provenance, request.buffer.range, .readOnly⟩,
   ⟨.loan, request.countSlot.provenance, request.countSlot.range, { write := true }⟩]

/-- Snapshot correspondence includes initialization, not merely byte equality. -/
def InputMatches (memory : MemoryState) (request : Request) : Prop :=
  ∀ i : Fin request.bytes.length,
    memory.cellAt? request.buffer.provenance.root (request.buffer.range.start + i.val) =
      some (request.bytes.toList[i.val]'i.isLt, true)

instance (memory : MemoryState) (request : Request) : Decidable (InputMatches memory request) :=
  by unfold InputMatches; infer_instance

structure Prepared (memory : MemoryState) (request : Request) where
  buffer : Resolved memory request.buffer
  countSlot : Resolved memory request.countSlot
  bufferSize : request.buffer.range.size = request.requested.toNat
  bytesSize : request.bytes.length = request.requested.toNat
  countSize : request.countSlot.range.size = 4
  bufferCPU : request.buffer.provenance.space = .cpuVirtual
  countCPU : request.countSlot.provenance.space = .cpuVirtual
  separated : buffer.physical.Disjoint countSlot.physical
  dedicated : memory.DedicatedBackings
  placement : ∀ root allocation, memory.allocations.lookup root = some allocation →
    allocation.live = true → allocation.space = .cpuVirtual →
    ∃ base, allocation.base = some base ∧ FitsAllocation base allocation.extent.stop
  allocationSeparation : ∀ left right a b leftBase rightBase,
    memory.allocations.lookup left = some a → memory.allocations.lookup right = some b →
    left ≠ right → a.live = true → b.live = true →
    a.space = .cpuVirtual → b.space = .cpuVirtual →
    a.base = some leftBase → b.base = some rightBase →
    (a.extent.shift leftBase.toNat).Disjoint (b.extent.shift rightBase.toNat)
  input : InputMatches memory request

def Prepared.transport {before after : MemoryState} {request : Request}
    (prepared : Prepared before request) (same : after.allocations = before.allocations)
    (backings : after.backings = before.backings) : Prepared after request where
  buffer := prepared.buffer.transport same backings
  countSlot := prepared.countSlot.transport same backings
  bufferSize := prepared.bufferSize
  bytesSize := prepared.bytesSize
  countSize := prepared.countSize
  bufferCPU := prepared.bufferCPU
  countCPU := prepared.countCPU
  separated := prepared.separated
  dedicated := by
    unfold MemoryState.DedicatedBackings MemoryState.backingCapacity?
    rw [same, backings]
    exact prepared.dedicated
  placement := by rw [same]; exact prepared.placement
  allocationSeparation := by rw [same]; exact prepared.allocationSeparation
  input := by
    intro i
    rw [MemoryState.cellAt?_of_maps_eq same backings]
    exact prepared.input i

/-- Exact pending occurrence; loan identities stay in the record, not recomputed.
Applicability of the synchronous handle and its ABI arguments remains separate. -/
structure PendingAt (state : CallProtocol.State Request) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) : Prop where
  lookup : state.pending.lookup call = some record
  custody : record.Valid state.machine.memory
  loans : record.loans.map Prod.snd =
    record.request.loans.map (fun loan => loan.grant record.caller record.agent)

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

structure Prefix (state : CallProtocol.State Request) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) where
  pending : PendingAt state call record
  prepared : Prepared state.machine.memory record.request
  clean : state.machine.violations.IsEmpty
  accepted : Nat
  bounded : accepted ≤ record.request.bytes.length

def Prefix.output {state : CallProtocol.State Request} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} (frontier : Prefix state call record) : Vec Byte :=
  record.request.bytes.take frontier.accepted

/-- A concrete provider memory action. Its identity and fault plan are retained. -/
structure Action where
  policy : StepPolicy
  operation : SomeOperation
  kind : ContextKind
  cause : EventCause
  faultAt : (sequence : SubstepSequence) → FaultPlan sequence

def Action.Runs (action : Action) (record : CallProtocol.Pending Request)
    (before after : CallProtocol.State Request) : Prop :=
  CallProtocol.step? before action.policy action.operation record.agent action.kind
    action.cause action.faultAt = some after

inductive CausalNode where
  | entry (call : CallProtocol.CallId)
  | returned (call : CallProtocol.CallId)
  | event (id : EventId)
deriving DecidableEq

def Represented (state : CallProtocol.State Request) : CausalNode → Prop
  | .entry call => ∃ caller agent loans,
      CallProtocol.Boundary.handoff call caller agent loans ∈ state.boundaries
  | .returned call => ∃ caller agent loans,
      CallProtocol.Boundary.returned call caller agent loans ∈ state.boundaries
  | .event id => ∃ event ∈ state.machine.events, event.event.id = id

/-- Select once outside a whole prefix derivation. No default relation is supplied. -/
structure CausalModel where
  precedes : CallProtocol.State Request → CausalNode → CausalNode → Prop

structure CausalModel.Valid (model : CausalModel) (state : CallProtocol.State Request) : Prop where
  endpoints : ∀ a b, model.precedes state a b → Represented state a ∧ Represented state b
  irreflexive : ∀ node, ¬ model.precedes state node node
  transitive : ∀ a b c, model.precedes state a b → model.precedes state b c →
    model.precedes state a c

structure HandoffCausality (model : CausalModel) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) (before after : CallProtocol.State Request) : Prop where
  beforeValid : model.Valid before
  afterValid : model.Valid after
  historyExtends : ∀ a b, model.precedes before a b → model.precedes after a b
  entry : CallProtocol.Boundary.handoff call record.caller record.agent record.ids ∈ after.boundaries
  callerEntry : ∀ old ∈ before.machine.events, old.event.context.id = record.caller →
    model.precedes after (.event old.event.id) (.entry call)

/-- Fixed graph obligations, including actual matched entry and exact new events.
Pending-prefix steps do not themselves establish a return edge.
Integrating these premises with `Grass.Op.step` is an open obligation. -/
structure CausalEvidence (model : CausalModel) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) (action : Action)
    (before after : CallProtocol.State Request) (added : List ValidMemoryEvent) : Prop where
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
    (event.event.kind.reads = true → event.event.provenance = record.request.buffer.provenance ∧
      record.request.buffer.range.Contains event.event.range) ∧
    (event.event.kind.writes = true → event.event.provenance = record.request.countSlot.provenance ∧
      record.request.countSlot.range.Contains event.event.range)
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
    CallProtocol.State Request → CallProtocol.State Request → Prop
  publishes : CallProtocol.CallId → CallProtocol.Pending Request → Action →
    CallProtocol.State Request → CallProtocol.State Request → Nat → Nat → Vec Byte → Prop

/-- Only count-slot bytes may change in this bounded provider slice. -/
def Confined (request : Request) (before after : MemoryState) : Prop :=
  ∀ root offset,
    (root ≠ request.countSlot.provenance.root ∨ ¬ request.countSlot.range.Covers offset) →
    after.cellAt? root offset = before.cellAt? root offset

structure CommittedStep (realization : Realization)
    {before after : CallProtocol.State Request} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request}
    (pre : Prefix before call record) (post : Prefix after call record)
    (action : Action) (output : Vec Byte) : Prop where
  ran : action.Runs record before after
  dispatch : realization.executesFor call record action before after
  publishes : realization.publishes call record action before after
    pre.accepted post.accepted output
  publication : Publication record.request.bytes pre.accepted post.accepted output
  obligations : after.machine.obligations = before.machine.obligations
  metadata : ∀ root, (after.machine.memory.allocations.lookup root).map AllocationRecord.metadata =
    (before.machine.memory.allocations.lookup root).map AllocationRecord.metadata
  confined : Confined record.request before.machine.memory after.machine.memory
  causal : ∃ added, CausalEvidence realization.causal call record action before after added

theorem CommittedStep.output_extends {realization : Realization}
    {before after : CallProtocol.State Request} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request}
    {pre : Prefix before call record} {post : Prefix after call record}
    {action : Action} {output : Vec Byte}
    (step : CommittedStep realization pre post action output) :
    pre.output ++ output = post.output := step.publication.append_prefix

theorem Prefix.no_denial {state : CallProtocol.State Request} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} (frontier : Prefix state call record) :
    state.machine.violations.records? = [] :=
  (AuditViolationLedger.isEmpty_iff_records?_nil _).mp frontier.clean

theorem PendingAt.same_record {state : CallProtocol.State Request} {call : CallProtocol.CallId}
    {left right : CallProtocol.Pending Request}
    (a : PendingAt state call left) (b : PendingAt state call right) : left = right := by
  exact Option.some.inj (a.lookup.symm.trans b.lookup)

/-- Reachable evidence starts at the actual handoff with zero accepted bytes.
The outer realization is fixed across the entire derivation. An arbitrary
`Prefix` alone must never be advertised as a reachable provider history. -/
inductive History (realization : Realization) (initial : CallProtocol.State Request)
    (call : CallProtocol.CallId) (record : CallProtocol.Pending Request) :
    {state : CallProtocol.State Request} → Prefix state call record → Type 1 where
  | handoff {state : CallProtocol.State Request} (frontier : Prefix state call record)
      (ran : CallProtocol.handoff? initial record.caller record.agent record.request
        record.request.loans = some (call, state))
      (input : Prepared initial.machine.memory record.request)
      (causal : HandoffCausality realization.causal call record initial state)
      (zero : frontier.accepted = 0) : History realization initial call record frontier
  | step {before after : CallProtocol.State Request}
      {pre : Prefix before call record} {post : Prefix after call record}
      (history : History realization initial call record pre)
      (action : Action) (output : Vec Byte)
      (committed : CommittedStep realization pre post action output) :
      History realization initial call record post

def History.published {realization : Realization} {initial : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    (history : History realization initial call record frontier) : Vec Byte :=
  match history with
  | .handoff .. => .fromList []
  | .step previous _ output _ => previous.published ++ output

/-- Every finite derived history publishes exactly its cumulative request prefix,
not merely some bounded collection of bytes. -/
theorem History.published_eq_output {realization : Realization}
    {initial : CallProtocol.State Request} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {state : CallProtocol.State Request}
    {frontier : Prefix state call record}
    (history : History realization initial call record frontier) :
    history.published = frontier.output := by
  induction history with
  | handoff frontier _ _ _ zero => simp [History.published, Prefix.output, zero, Vec.empty]
  | step previous action output committed ih =>
    change previous.published ++ output = _
    rw [ih]
    exact committed.output_extends

theorem History.causal_valid {realization : Realization}
    {initial : CallProtocol.State Request} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {state : CallProtocol.State Request}
    {frontier : Prefix state call record}
    (history : History realization initial call record frontier) : realization.causal.Valid state := by
  cases history with
  | handoff _ _ _ causal _ => exact causal.afterValid
  | step _ _ _ committed => obtain ⟨_, causal⟩ := committed.causal; exact causal.afterValid

end Grass.Platform.Win32.WriteFile
