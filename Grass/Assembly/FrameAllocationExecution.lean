import Grass.Assembly.SourcePrologue
import Grass.ISA.X86.Execution.SubRspNormal

/-! Connect an actual fetched normal SUB RSP receipt to the allocation computed
by the frame layout. No literal frame amount or instruction offset is supplied.
This does not establish entry reachability or exclude other execution branches. -/

namespace Grass.Assembly.FrameAllocation
open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Memory

/-- Actual observed allocation bytes determine the typed decoded instruction;
the caller does not supply a second instruction-selection assertion. -/
theorem allocation_encoding_of_observation (allocation : Resolved) {before : State}
    {afterFetch : MachineState} (fetch : FetchedSite before afterFetch)
    (observed : fetch.run.complete.committed.observed = some allocation.encoding.toBytes) :
    fetch.site.encoding = allocation.encoding := by
  have bytes := Option.some.inj (fetch.observed_exact.symm.trans observed)
  have decoded := (congrArg decodeInsn fetch.site.bytesExact).symm.trans fetch.site.decoded
  rw [fetch.noTrailing, List.append_nil] at decoded
  rw [bytes] at decoded
  have expected := encoding_decodes allocation []
  rw [List.append_nil] at expected
  exact congrArg Prod.fst (Except.ok.inj (decoded.symm.trans expected))

/-- `rsp_allocation_exact` uses the resolved layout's signed-immediate proof. -/
theorem rsp_allocation_exact (allocation : Resolved) {before : State}
    {afterFetch afterCompute : MachineState}
    (receipt : SubRspNormal before afterFetch afterCompute allocation.immediate) :
    receipt.result.gpr .rsp = before.gpr .rsp -
      BitVec.ofNat 64 allocation.layout.callAllocationBytes := by
  rw [receipt.rsp_exact, allocation.amountExact, BitVec.ofInt_natCast]

/-- The bytes belong to this layout-derived encoding at the actual fetched site. -/
theorem fetched_allocation_bytes (allocation : Resolved) {before : State}
    {afterFetch afterCompute : MachineState}
    (receipt : SubRspNormal before afterFetch afterCompute allocation.immediate) :
    ∃ valid, afterFetch.events = before.machine.events ++ [valid] ∧
      valid.event.valueRead = some allocation.encoding.toBytes :=
  receipt.fetched_event

/-- `rsp_allocation_natural` derives ordinary address subtraction when the
actual starting register can cover the derived allocation without wrap. -/
theorem rsp_allocation_natural (allocation : Resolved) {before : State}
    {afterFetch afterCompute : MachineState}
    (receipt : SubRspNormal before afterFetch afterCompute allocation.immediate)
    (fits : allocation.layout.callAllocationBytes ≤ (before.gpr .rsp).toNat) :
    (receipt.result.gpr .rsp).toNat =
      (before.gpr .rsp).toNat - allocation.layout.callAllocationBytes := by
  have bounded : allocation.layout.callAllocationBytes < 2 ^ 64 :=
    Nat.lt_of_le_of_lt fits (before.gpr .rsp).isLt
  have exactAmount : (BitVec.ofNat 64 allocation.layout.callAllocationBytes).toNat =
      allocation.layout.callAllocationBytes := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
  rw [rsp_allocation_exact allocation receipt, BitVec.toNat_sub_of_le]
  · rw [exactAmount]
  · simpa only [BitVec.le_def, exactAmount] using fits

/-- The same receipt uses the frame parsed by the source-prologue generator. -/
theorem source_prologue_allocation (prologue : SourcePrologue.Result) {before : State}
    {afterFetch afterCompute : MachineState}
    (receipt : SubRspNormal before afterFetch afterCompute prologue.allocation.immediate) :
    receipt.result.gpr .rsp = before.gpr .rsp -
      BitVec.ofNat 64 prologue.frame.layout.callAllocationBytes := by
  rw [rsp_allocation_exact prologue.allocation receipt,
    resolve?_layout prologue.allocationExact]

end Grass.Assembly.FrameAllocation
