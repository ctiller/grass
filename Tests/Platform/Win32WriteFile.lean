import Grass.Platform.Win32.WriteFile
import Tests.Memory.CallProtocol

namespace Grass.Tests.Win32WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.WriteFile
open Grass.Tests.Spike1

def bytes : Vec Byte := .fromList [11, 22, 33]
def allocation : AllocationRecord :=
  { Tests.Memory.Spike1Block.stackRecord with
    bytes := ByteStore.empty.write 0 bytes.toList true }
def memory : MemoryState :=
  (MemoryState.empty.allocate? stackAlloc allocation).getD .empty
def request : Request :=
  { handle := 123, requested := 3, bytes := bytes
    buffer := ⟨stackProvenance, ⟨0, 3⟩⟩
    countSlot := ⟨stackProvenance, ⟨16, 4⟩⟩ }

theorem lookup_exact (root : AllocId) :
    memory.allocations.lookup root = if root = stackAlloc then some allocation else none := by
  simp [memory, MemoryState.allocate?, MemoryState.empty, FiniteMap.lookup_insert]

def resolved (range : ByteRange) (contained : stackProvenance.extent.Contains range) :
    Resolved memory ⟨stackProvenance, range⟩ where
  allocation := allocation
  lookup := by change memory.allocations.lookup stackAlloc = some allocation; decide
  live := rfl
  epoch := rfl
  space := rfl
  source := rfl
  extent := rfl
  nested := by change stackProvenance.Nested; decide
  contained := contained
  base := stackBaseAddress
  placed := rfl
  noWrap := by decide

def prepared : Prepared memory request where
  buffer := resolved ⟨0, 3⟩ (by decide)
  countSlot := resolved ⟨16, 4⟩ (by decide)
  bufferSize := rfl
  bytesSize := rfl
  countSize := rfl
  bufferCPU := rfl
  countCPU := rfl
  separated := by decide
  unaliased := rfl
  placement := by
    intro root record found _ _
    rw [lookup_exact] at found
    split at found
    · cases found
      exact ⟨stackBaseAddress, rfl, by decide⟩
    · contradiction
  allocationSeparation := by
    intro left right a b lb rb ha hb different
    rw [lookup_exact] at ha hb
    split at ha <;> split at hb <;> simp_all
  input := by decide

def initial : CallProtocol.State Request :=
  CallProtocol.initial ((MachineState.initial memory).noteContext mainThread .thread)
    FreshSupply.initial (by decide)
def handed := CallProtocol.handoff? initial mainThread apiAgent request request.loans

theorem handoff_exists : handed.isSome := by decide

def call := (handed.get handoff_exists).1
def pending := (handed.get handoff_exists).2
def record : CallProtocol.Pending Request :=
  (pending.pending.lookup call).get (by decide)

def initialPrefix : Prefix pending call record where
  pending := ⟨rfl, by decide, by decide⟩
  prepared := prepared.transport rfl rfl
  clean := by decide
  accepted := 0
  bounded := by decide

/-- No real ordering or output is claimed by the start-only fixture. -/
def noEffects : Realization where
  causal := ⟨fun _ _ _ => False⟩
  executesFor := fun selected _ _ _ _ => selected = call
  publishes := fun _ _ _ _ _ before after output => before = after ∧ output = .fromList []

theorem noEffects_valid (state : CallProtocol.State Request) : noEffects.causal.Valid state :=
  ⟨by intros _ _ h; exact False.elim h,
   by intros _ h; exact h,
   by intros _ _ _ h; exact False.elim h⟩

theorem handoffCausality : HandoffCausality noEffects.causal call record initial pending where
  beforeValid := noEffects_valid initial
  afterValid := noEffects_valid pending
  historyExtends := by intros _ _ h; exact False.elim h
  entry := List.mem_cons_self
  callerEntry := by intro old present; change old ∈ [] at present; contradiction

def startHistory : History noEffects initial call record initialPrefix :=
  .handoff initialPrefix rfl prepared handoffCausality rfl

theorem initial_output_empty : initialPrefix.output = .fromList [] := rfl

def quietAction : Action where
  policy := Grass.Tests.Spike1Policy.policy
  operation := SomeOperation.of Grass.Tests.Spike1Policy.Op.leaPayload
  kind := .externalAgent
  cause := ⟨⟨"writefile.quiet"⟩⟩
  faultAt := fun _ => .none

def quietResult := CallProtocol.step? pending quietAction.policy quietAction.operation
  apiAgent quietAction.kind quietAction.cause quietAction.faultAt
def quietState := quietResult.get (by decide)
def quietPrefix : Prefix quietState call record where
  pending := ⟨rfl, by decide, by decide⟩
  prepared := prepared.transport rfl rfl
  clean := by decide
  accepted := 0
  bounded := by decide

/-- A real checked no-memory action inhabits the conditional step interface.
It supplies no evidence that a cross-context memory write is accepted. -/
theorem quietStep : CommittedStep noEffects initialPrefix quietPrefix quietAction (.fromList []) where
  ran := rfl
  dispatch := rfl
  publishes := ⟨rfl, rfl⟩
  publication := ⟨by decide, by decide, rfl⟩
  obligations := rfl
  metadata := by intro root; rfl
  confined := by intro root offset _; rfl
  causal := ⟨[], {
    entry := List.mem_cons_self
    events := rfl
    fresh := by intro event present; contradiction
    beforeValid := noEffects_valid pending
    afterValid := noEffects_valid quietState
    historyExtends := by intros _ _ h; exact False.elim h
    callerEntry := by intro old present; change old ∈ [] at present; contradiction
    entryEffects := by intro event present; contradiction
    footprint := by intro event present; contradiction
    conflicts := by intro old present; change old ∈ [] at present; contradiction }⟩

def quietHistory : History noEffects initial call record quietPrefix :=
  .step startHistory quietAction (.fromList []) quietStep

theorem missing_entry_edge_rejected {added : List ValidMemoryEvent}
    (event : ValidMemoryEvent) (present : event ∈ added) :
    ¬ CausalEvidence noEffects.causal call record quietAction pending quietState added := by
  intro h
  exact (h.entryEffects event present).2

theorem wrong_occurrence_dispatch_rejected :
    ¬ noEffects.executesFor pending.callSupply.fresh.1 record quietAction pending quietState := by
  change pending.callSupply.fresh.1 ≠ call
  decide

theorem quiet_history_output : quietHistory.published = quietPrefix.output :=
  quietHistory.published_eq_output

theorem cyclic_initial_graph_rejected :
    ¬ (CausalModel.mk (fun _ _ _ => True)).Valid initial := by
  intro valid
  exact valid.irreflexive (.entry call) trivial

theorem missing_loan_rejected :
    ¬ PendingAt pending call { record with loans := [] } := by
  intro h
  have same := PendingAt.same_record initialPrefix.pending h
  have bad := congrArg (fun r => r.loans.length) same
  contradiction

theorem invented_accepted_start_rejected :
    ¬ ({ initialPrefix with accepted := 1, bounded := by decide } : Prefix pending call record).accepted = 0 := by
  decide

theorem wrong_call_rejected : ∀ call state, handed = some (call, state) →
    state.pending.lookup state.callSupply.fresh.1 = none := by
  intro call state found
  cases found
  decide

theorem initialized_bytes_match : InputMatches memory request := prepared.input

theorem uninitialized_input_rejected :
    ¬ InputMatches Tests.Memory.Spike1Block.state₀ request := by decide

theorem substituted_bytes_rejected :
    ¬ InputMatches memory { request with bytes := .fromList [11, 99, 33] } := by decide

theorem overlapping_slot_rejected :
    ¬ (resolved ⟨0, 3⟩ (by decide)).physical.Disjoint
      (resolved ⟨2, 4⟩ (by decide)).physical := by decide

theorem first_chunk : Publication bytes 0 1 (.fromList [11]) :=
  ⟨by decide, by decide, rfl⟩
theorem next_chunk : Publication bytes 1 3 (.fromList [22, 33]) :=
  ⟨by decide, by decide, rfl⟩
theorem zero_progress : Publication bytes 1 1 (.fromList []) :=
  ⟨by decide, by decide, rfl⟩
theorem duplicated_prefix_rejected : ¬ Publication bytes 1 2 (.fromList [11]) := by
  intro h
  have bad := h.suffix
  contradiction
theorem excess_publication_rejected : ¬ Publication bytes 0 4 (.fromList [11, 22, 33]) := by
  intro h
  have bad := h.bounded
  contradiction
theorem backwards_publication_rejected : ¬ Publication bytes 2 1 (.fromList []) := by
  intro h
  have bad := h.monotone
  omega

/-- Abstractly setting an ordering relation to True fails its fixed obligations. -/
theorem universal_order_rejected (state : CallProtocol.State Request) :
    ¬ (∀ node : CausalNode, ¬ (fun (_ : CallProtocol.State Request) _ _ => True) state node node) := by
  intro h
  exact h (.entry FreshSupply.initial.fresh.1) trivial

/-- The actual current checker retains the cross-context denial despite loans.
This fixture uses the same typed request and count-slot loan as the prefix. -/
def countWrite : AccessDescriptor :=
  Grass.Tests.Spike1.access stackProvenance ⟨16, 4⟩
    (addressOf stackBaseAddress 16) .write .readWrite 4 false true

inductive CountOp where
  | caller | provider

instance : HasOperationFacets CountOp where
  facets op :=
    { memoryEffects := some (.single { countWrite with context :=
        match op with | .caller => mainThread | .provider => apiAgent })
      faults := some [.pageFault, .generalProtection]
      restartability := some .notRestartable, ordering := some .plain }

def zeroPolicy : StepPolicy :=
  { Grass.Tests.Spike1Policy.policy with
    oracle := .ofMemory (fun _ d => List.replicate d.range.size 0) (fun _ _ _ => 0) }

def zeroedOutcome := Grass.Op.step zeroPolicy initial.machine (SomeOperation.of CountOp.caller)
  mainThread .thread ⟨⟨"writefile.zero"⟩⟩
def zeroedMachine := zeroedOutcome.state?.get (by decide)
def zeroed : CallProtocol.State Request :=
  CallProtocol.initial zeroedMachine FreshSupply.initial (by decide)
def handedAfterZero := CallProtocol.handoff? zeroed mainThread apiAgent request request.loans
def afterZero := (handedAfterZero.get (by decide)).2
def denied := CallProtocol.step? afterZero zeroPolicy (SomeOperation.of CountOp.provider)
  apiAgent .externalAgent ⟨⟨"writefile.zero"⟩⟩ (fun _ => .none)

theorem caller_zero_clean : zeroedMachine.violations.IsEmpty := by decide
theorem provider_step_some_but_denied : denied.isSome ∧
    ¬ (denied.get (by decide)).machine.violations.IsEmpty := by
  exact ⟨by decide, by decide⟩

theorem provider_denial_is_the_ordering_blocker :
    (denied.get (by decide)).machine.violations.records?.map (fun item => item.class_) =
      [.conflictingAccess] := by decide

theorem denied_not_a_prefix (occurrence : CallProtocol.CallId)
    (pendingRecord : CallProtocol.Pending Request) :
    ¬ Nonempty (Prefix (denied.get (by decide)) occurrence pendingRecord) := by
  rintro ⟨frontier⟩
  exact provider_step_some_but_denied.2 frontier.clean

end Grass.Tests.Win32WriteFile
