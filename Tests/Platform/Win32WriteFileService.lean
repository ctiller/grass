import Grass.Platform.Win32.WriteFileService
import Tests.Platform.Win32WriteFile

namespace Grass.Tests.Win32WriteFileService

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32 Grass.Platform.Win32.ExecutionState
open Grass.Platform.Win32.WriteFile
open Grass.Tests.Spike1

def returnSlot : Argument := ⟨stackProvenance, ⟨128, 8⟩⟩
def homeSlot : Argument := ⟨stackProvenance, ⟨136, 32⟩⟩
def fifthSlot : Argument := ⟨stackProvenance, ⟨168, 8⟩⟩

/-- These are exactly the three extra ABI custody requests.  The fixture does
not claim that a native `CALL` reached these coordinates. -/
def runtime : WriteFileRuntime where
  entryRsp := 0
  continuation := 0
  returnSlot := returnSlot
  homeSlot := homeSlot
  saved := fun _ => 0
  fifthSlot := fifthSlot
  accepted := 0

theorem runtime_has_exact_three_abi_extras : runtime.loanPlan.additional =
    [⟨.loan, stackProvenance, ⟨128, 8⟩, .readOnly⟩,
     ⟨.loan, stackProvenance, ⟨136, 32⟩, .readWrite⟩,
     ⟨.loan, stackProvenance, ⟨168, 8⟩, .readOnly⟩] := rfl

theorem runtime_full_batch_has_two_semantic_plus_three_abi :
    (runtime.loanPlan.requests Grass.Tests.Win32WriteFile.request).length = 5 := by decide

def handed := CallProtocol.handoff? Grass.Tests.Win32WriteFile.initial mainThread apiAgent
  (.writeFile Grass.Tests.Win32WriteFile.request)
  (runtime.loanPlan.requests Grass.Tests.Win32WriteFile.request)

theorem full_batch_handoff_exists : handed.isSome := by decide

def call := (handed.get full_batch_handoff_exists).1
def protocol₀ := (handed.get full_batch_handoff_exists).2
def record : CallProtocol.Pending Request :=
  ((protocol₀.pending.lookup call).bind selectPending).get (by decide)

def prefix₀ : Prefix runtime.loanPlan protocol₀ call record where
  pending := ⟨rfl, by decide, ⟨by decide⟩⟩
  prepared := Grass.Tests.Win32WriteFile.prepared.transport rfl rfl
  clean := by decide
  accepted := 0
  bounded := by decide

def action := Grass.Tests.Win32WriteFile.quietAction
def result₁ := CallProtocol.step? protocol₀ action.policy action.operation
  apiAgent action.kind action.cause action.faultAt
def protocol₁ := result₁.get (by decide)
def prefix₁ : Prefix runtime.loanPlan protocol₁ call record where
  pending := ⟨rfl, by decide, ⟨by decide⟩⟩
  prepared := Grass.Tests.Win32WriteFile.prepared.transport rfl rfl
  clean := by decide
  accepted := 0
  bounded := by decide

theorem step₁ : CommittedStep Grass.Tests.Win32WriteFile.noEffects prefix₀ prefix₁ action (.fromList []) where
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
    beforeValid := Grass.Tests.Win32WriteFile.noEffects_valid protocol₀
    afterValid := Grass.Tests.Win32WriteFile.noEffects_valid protocol₁
    historyExtends := by intros _ _ h; exact False.elim h
    callerEntry := by intro old present; change old ∈ [] at present; contradiction
    entryEffects := by intro event present; contradiction
    footprint := by intro event present; contradiction
    conflicts := by intro old present; change old ∈ [] at present; contradiction }⟩

def unrelatedCall := protocol₀.callSupply.fresh.1

theorem unrelated_call_is_distinct : unrelatedCall ≠ call := by decide

def cpu₀ : Grass.ISA.X86.Execution.State :=
  { machine := protocol₀.machine, gpr := fun _ => 0, rip := 0, rflags := 0 }

def checked₀ : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol protocol₀ cpu₀ rfl
    (.pending call record.caller record.agent)

def before : RawState := checked₀.raw
  ((FiniteMap.empty.insert unrelatedCall .exitProcess).insert call (.writeFile runtime))

/-- The unrelated table entry exercises framing only.  It intentionally has no
matching protocol pending record, so this fixture makes no `RuntimeLinked` claim. -/
theorem before_has_unrelated_runtime_entry :
    before.calls.lookup unrelatedCall = some .exitProcess := by rfl

def receipt₁ : ServiceReceipt Grass.Tests.Win32WriteFile.noEffects before call record action (.fromList []) where
  protocol := protocol₀
  projected := CallProtocol.State.metadata_pack? protocol₀
  runtime := runtime
  runtimeLookup := rfl
  control := rfl
  pre := prefix₀
  accepted := rfl
  nextProtocol := protocol₁
  post := prefix₁
  committed := step₁

theorem receipt₁_tracks_actual_post_frontier : receipt₁.nextRuntime.accepted = prefix₁.accepted := rfl
theorem receipt₁_preserves_plan : receipt₁.nextRuntime.loanPlan = runtime.loanPlan := rfl
theorem receipt₁_preserves_frame : receipt₁.nextRuntime.toReturnFrame = runtime.toReturnFrame := rfl
theorem receipt₁_preserves_fifth : receipt₁.nextRuntime.fifthSlot = fifthSlot := rfl
theorem receipt₁_preserves_unrelated_runtime :
    receipt₁.after.calls.lookup unrelatedCall = some .exitProcess := by
  rw [receipt₁.after_otherCall unrelated_call_is_distinct]
  rfl

def result₂ := CallProtocol.step? protocol₁ action.policy action.operation
  apiAgent action.kind action.cause action.faultAt
def protocol₂ := result₂.get (by decide)
def prefix₂ : Prefix runtime.loanPlan protocol₂ call record where
  pending := ⟨rfl, by decide, ⟨by decide⟩⟩
  prepared := Grass.Tests.Win32WriteFile.prepared.transport rfl rfl
  clean := by decide
  accepted := 0
  bounded := by decide

theorem step₂ : CommittedStep Grass.Tests.Win32WriteFile.noEffects prefix₁ prefix₂ action (.fromList []) where
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
    beforeValid := Grass.Tests.Win32WriteFile.noEffects_valid protocol₁
    afterValid := Grass.Tests.Win32WriteFile.noEffects_valid protocol₂
    historyExtends := by intros _ _ h; exact False.elim h
    callerEntry := by intro old present; change old ∈ [] at present; contradiction
    entryEffects := by intro event present; contradiction
    footprint := by intro event present; contradiction
    conflicts := by intro old present; change old ∈ [] at present; contradiction }⟩

def receipt₂ : ServiceReceipt Grass.Tests.Win32WriteFile.noEffects receipt₁.after call record action (.fromList []) where
  protocol := protocol₁
  projected := receipt₁.after_projected
  runtime := receipt₁.nextRuntime
  runtimeLookup := receipt₁.after_runtimeLookup
  control := receipt₁.after_control
  pre := prefix₁
  accepted := rfl
  nextProtocol := protocol₂
  post := prefix₂
  committed := step₂

theorem consecutive_receipts_share_frontier_and_plan :
    receipt₂.pre.accepted = receipt₁.post.accepted ∧
      receipt₂.runtime.loanPlan = receipt₁.runtime.loanPlan :=
  receipt₁.frontier_continuity receipt₂

/-- Any receipt at this exact raw state must use the runtime stored under the
actual call identity; its runtime field cannot be independently invented. -/
theorem every_receipt_uses_actual_runtime {chosenAction : Action} {output : Vec Byte}
    (receipt : ServiceReceipt Grass.Tests.Win32WriteFile.noEffects before call record
      chosenAction output) : receipt.runtime = runtime := by
  exact CallRuntime.writeFile.inj (Option.some.inj
    (receipt.runtimeLookup.symm.trans
      (show before.calls.lookup call = some (.writeFile runtime) from rfl)))

theorem every_receipt_starts_at_actual_zero {chosenAction : Action} {output : Vec Byte}
    (receipt : ServiceReceipt Grass.Tests.Win32WriteFile.noEffects before call record
      chosenAction output) : receipt.pre.accepted = 0 := by
  calc
    receipt.pre.accepted = receipt.runtime.accepted := receipt.accepted
    _ = runtime.accepted := congrArg WriteFileRuntime.accepted
      (every_receipt_uses_actual_runtime receipt)
    _ = 0 := rfl

theorem invented_runtime_frontier_rejected {chosenAction : Action} {output : Vec Byte}
    (receipt : ServiceReceipt Grass.Tests.Win32WriteFile.noEffects before call record
      chosenAction output) : ¬ receipt.runtime.accepted = 1 := by
  rw [every_receipt_uses_actual_runtime receipt]
  decide

end Grass.Tests.Win32WriteFileService
