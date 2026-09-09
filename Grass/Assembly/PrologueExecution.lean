import Grass.Assembly.FrameAllocationExecution
import Grass.ISA.X86.Execution.PushNormal

/-! Proof-bearing continuous normal execution of a source-derived prologue.
Every edge is an actual fetched normal receipt. Construction is conditional and
does not establish entry reachability, totality, or source-byte membership. -/

namespace Grass.Assembly.PrologueExecution

open Grass.ABI.Win64 Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Memory

/-- A continuous finite sequence of actual register PUSH receipts. -/
inductive PushRun : List Gpr → State → State → Type 1 where
  | nil (state : State) : PushRun [] state state
  | cons {before after : State} {afterFetch afterStore : MachineState}
      {register : Gpr} {registers : List Gpr}
      (push : PushNormal before afterFetch afterStore register)
      (rest : PushRun registers push.result after) :
      PushRun (register :: registers) before after

namespace PushRun

/-- The index list counts exactly the actual PUSH receipts. -/
def count {registers : List Gpr} {before after : State}
    (run : PushRun registers before after) : Nat :=
  match run with
  | .nil _ => 0
  | .cons _ rest => rest.count + 1

@[simp] theorem count_exact {registers : List Gpr} {before after : State}
    (run : PushRun registers before after) : run.count = registers.length := by
  induction run with
  | nil => rfl
  | cons push rest ih => simp [count, ih]

/-- The local no-underflow premise on every actual receipt composes to a bound
for the complete saved-register prefix. -/
theorem stack_fits {registers : List Gpr} {before after : State}
    (run : PushRun registers before after) :
    8 * registers.length ≤ (before.gpr .rsp).toNat := by
  induction run with
  | nil => simp
  | @cons before after afterFetch afterStore register registers push rest ih =>
      have nextRsp := push.rsp_toNat
      have localBound := push.stackNoUnderflow
      simp only [List.length_cons]
      omega

/-- Receipt-local underflow checks compose to the exact natural stack delta. -/
theorem rsp_toNat {registers : List Gpr} {before after : State}
    (run : PushRun registers before after) :
    (after.gpr .rsp).toNat = (before.gpr .rsp).toNat - 8 * registers.length := by
  induction run with
  | nil => simp
  | @cons before after afterFetch afterStore register registers push rest ih =>
      have restFits := rest.stack_fits
      rw [ih, push.rsp_toNat]
      have localBound := push.stackNoUnderflow
      simp only [List.length_cons]
      omega

/-- Every non-RSP register is framed through the complete receipt chain. -/
theorem gpr_frame {registers : List Gpr} {before after : State}
    (run : PushRun registers before after) (register : Gpr) (other : register ≠ .rsp) :
    after.gpr register = before.gpr register := by
  induction run with
  | nil => rfl
  | @cons before after afterFetch afterStore pushed registers push rest ih =>
      exact ih.trans (push.gpr_frame register other)

/-- The final event list extends the initial one by exactly the two completed
events retained by each PUSH receipt, without replacing either memory state. -/
theorem events_append {registers : List Gpr} {before after : State}
    (run : PushRun registers before after) :
    ∃ added, after.machine.events = before.machine.events ++ added ∧
      added.length = 2 * registers.length := by
  induction run with
  | nil => exact ⟨[], by simp, rfl⟩
  | @cons before after afterFetch afterStore register registers push rest ih =>
      obtain ⟨fetched, stored, pushedEvents, _, _⟩ := push.events_exact
      obtain ⟨tail, tailEvents, tailLength⟩ := ih
      refine ⟨[fetched, stored] ++ tail, ?_, ?_⟩
      · rw [tailEvents, pushedEvents, List.append_assoc]
      · simp only [List.length_append, List.length_cons, List.length_nil, tailLength]
        omega

end PushRun

/-- Exact saved-register PUSH sequence followed by the actual layout-derived
SUB RSP allocation receipt. -/
structure Result (prologue : SourcePrologue.Result) (before after : State) where
  afterPushes : State
  pushes : PushRun prologue.frame.saved.registers before afterPushes
  afterAllocationFetch : MachineState
  afterAllocationCompute : MachineState
  allocation : SubRspNormal afterPushes afterAllocationFetch afterAllocationCompute
    prologue.allocation.immediate
  allocationFits : prologue.frame.layout.callAllocationBytes ≤
    (afterPushes.gpr .rsp).toNat
  afterExact : after = allocation.result

/-- The actual receipt-local bounds cover the complete source frame before any
natural subtraction is used. -/
theorem Result.totalFrame_fits {prologue : SourcePrologue.Result} {before after : State}
    (result : Result prologue before after) :
    prologue.frame.layout.totalFrameBytes ≤ (before.gpr .rsp).toNat := by
  have pushed := result.pushes.rsp_toNat
  have pushesFit := result.pushes.stack_fits
  have allocationFit := result.allocationFits
  simp only [CallFrameLayout.totalFrameBytes, prologue.frame.layout_saved]
  omega

/-- The complete normal prologue subtracts exactly the source frame's derived
total size, with no literal register count or allocation amount. -/
theorem Result.rsp_totalFrameBytes {prologue : SourcePrologue.Result} {before after : State}
    (result : Result prologue before after) :
    (after.gpr .rsp).toNat =
      (before.gpr .rsp).toNat - prologue.frame.layout.totalFrameBytes := by
  rw [result.afterExact]
  have allocated := FrameAllocation.rsp_allocation_natural prologue.allocation
    result.allocation (by
      rw [FrameAllocation.resolve?_layout prologue.allocationExact]
      exact result.allocationFits)
  rw [allocated, result.pushes.rsp_toNat]
  rw [FrameAllocation.resolve?_layout prologue.allocationExact]
  simp only [CallFrameLayout.totalFrameBytes, prologue.frame.layout_saved]
  omega

/-- Registers other than RSP are framed by every PUSH and the allocation SUB. -/
theorem Result.gpr_frame {prologue : SourcePrologue.Result} {before after : State}
    (result : Result prologue before after) (register : Gpr) (other : register ≠ .rsp) :
    after.gpr register = before.gpr register := by
  rw [result.afterExact]
  exact (result.allocation.gpr_frame register other).trans
    (result.pushes.gpr_frame register other)

/-- The final full RFLAGS value is the actual allocation receipt's normal SUB result. -/
theorem Result.rflags_exact {prologue : SourcePrologue.Result} {before after : State}
    (result : Result prologue before after) :
    after.rflags = completedSubRflags result.afterPushes prologue.allocation.immediate := by
  exact (congrArg (fun state => state.rflags) result.afterExact).trans
    result.allocation.rflags_exact

/-- The complete prologue event history is the actual PUSH fetch/store pairs
followed by the actual allocation fetch event. -/
theorem Result.events_append {prologue : SourcePrologue.Result} {before after : State}
    (result : Result prologue before after) :
    ∃ added, after.machine.events = before.machine.events ++ added ∧
      added.length = 2 * prologue.frame.saved.registers.length + 1 := by
  obtain ⟨pushed, pushedEvents, pushedLength⟩ := result.pushes.events_append
  obtain ⟨allocated, allocationEvents, _⟩ := result.allocation.events_exact
  refine ⟨pushed ++ [allocated], ?_, ?_⟩
  · rw [congrArg (fun state => state.machine.events) result.afterExact,
      allocationEvents, pushedEvents, List.append_assoc]
  · simp [pushedLength]

end Grass.Assembly.PrologueExecution
