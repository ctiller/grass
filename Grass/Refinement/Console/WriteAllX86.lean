import Grass.ISA.X86.Execution.ArithmeticNormal
import Grass.ISA.X86.Execution.BranchNormal
import Grass.Std.Console.WriteAll
import Grass.Assembly.SourceFetch
import Grass.Refinement.Console.WriteFileObserved

/-! The authored write-all loop's continuous ADD/SUB/JMP normal suffix.
This consumes actual fetched receipts. It does not construct a caller return,
prove source-site reachability, or replace the instruction factory.
-/

namespace Grass.Refinement.Console.WriteAllX86

open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Memory Grass.Std.Console Grass.Std.Logical

/-- Both authored TEST EAX,EAX guards inspect the low DWORD. Undefined AF
cannot affect their branch decision. -/
theorem test_eax_zero {before : State} {afterFetch afterCompute : MachineState}
    (receipt : ArithmeticNormal before afterFetch afterCompute (.test .w32 .rax .rax)) :
    receipt.result.statusFlags.zf = ((before.gpr .rax).setWidth 32 == 0) := by
  have zeroFlag := receipt.flags_conform.2.2.2.1
  change (some (((before.gpr .rax).setWidth 32 &&& (before.gpr .rax).setWidth 32) == 0) = none ∨
    some (((before.gpr .rax).setWidth 32 &&& (before.gpr .rax).setWidth 32) == 0) =
      some receipt.result.statusFlags.zf) at zeroFlag
  have equation : ((before.gpr .rax).setWidth 32 == 0) = receipt.result.statusFlags.zf := by
    simpa only [BitVec.and_self, reduceCtorEq, false_or, Option.some.injEq] using zeroFlag
  exact equation.symm

/-- A conforming initialized count cannot take the authored unsigned excess
branch. This does not erase the violation branch from other executions. -/
theorem cmp_count_no_violation {before : State} {afterFetch afterCompute : MachineState}
    (receipt : ArithmeticNormal before afterFetch afterCompute (.cmp .w32 .rax .r14))
    (bounded : ((before.gpr .rax).setWidth 32).toNat ≤ ((before.gpr .r14).setWidth 32).toNat)
    (displacement : BitVec 32) :
    (BranchInstruction.above displacement).taken receipt.result.statusFlags = false := by
  have carry := receipt.flags_conform.1
  have zeroFlag := receipt.flags_conform.2.2.2.1
  change (some (decide (((before.gpr .rax).setWidth 32).toNat < ((before.gpr .r14).setWidth 32).toNat)) = none ∨
    some (decide (((before.gpr .rax).setWidth 32).toNat < ((before.gpr .r14).setWidth 32).toNat)) =
      some receipt.result.statusFlags.cf) at carry
  change (some (((before.gpr .rax).setWidth 32 - (before.gpr .r14).setWidth 32) == 0) = none ∨
    some (((before.gpr .rax).setWidth 32 - (before.gpr .r14).setWidth 32) == 0) =
      some receipt.result.statusFlags.zf) at zeroFlag
  by_cases same : (before.gpr .rax).setWidth 32 = (before.gpr .r14).setWidth 32
  · have zero : receipt.result.statusFlags.zf = true := by simpa [same] using zeroFlag.symm
    simp [BranchInstruction.taken, zero]
  · have strict : ((before.gpr .rax).setWidth 32).toNat < ((before.gpr .r14).setWidth 32).toNat := by
      have different := BitVec.toNat_ne_iff_ne.mpr same
      omega
    have carried : true = receipt.result.statusFlags.cf := by
      simpa only [strict, decide_true, reduceCtorEq, false_or, Option.some.injEq] using carry
    simp [BranchInstruction.taken, carried]

/-- Numeric part of the authored r13/r14d cursor placement. The full 64-bit
remaining equality retains the required zero extension. -/
structure CursorRegisters (payload : Vec Byte) (base : Nat)
    (cursor : WriteCursor payload) (state : State) : Prop where
  pointer : (state.gpr .r13).toNat = base + cursor.committed
  remaining : (state.gpr .r14).toNat = cursor.remaining.length
  addressFits : base + payload.length < 2 ^ 64
  countFits : payload.length < 2 ^ 32

/-- Each receipt starts at the actual result of its predecessor. The jump's
source-resolved target remains an explicit consumer obligation. -/
structure UpdateRun (before : State) where
  addFetch : MachineState
  addCompute : MachineState
  add : ArithmeticNormal before addFetch addCompute (.add .w64 .r13 .rax)
  subFetch : MachineState
  subCompute : MachineState
  subtract : ArithmeticNormal add.result subFetch subCompute (.sub .w32 .r14 .rax)
  jumpFetch : MachineState
  jumpCompute : MachineState
  displacement : BitVec 32
  jump : BranchNormal subtract.result jumpFetch jumpCompute (.jump displacement)

def UpdateRun.result {before : State} (run : UpdateRun before) : State := run.jump.result

theorem UpdateRun.pointer_exact {before : State} (run : UpdateRun before) :
    run.result.gpr .r13 = before.gpr .r13 + before.gpr .rax := by
  have addEq := run.add.destination_exact
  change run.add.result.gpr .r13 = before.gpr .r13 + before.gpr .rax at addEq
  exact (congrFun run.jump.gpr_frame .r13).trans
    ((run.subtract.gpr_frame .r13 (by decide)).trans addEq)

theorem UpdateRun.remaining_exact {before : State} (run : UpdateRun before) :
    run.result.gpr .r14 =
      ((before.gpr .r14).setWidth 32 - (before.gpr .rax).setWidth 32).setWidth 64 := by
  have subEq := run.subtract.destination_exact
  change run.subtract.result.gpr .r14 =
    0#32 ++ ((run.add.result.gpr .r14).setWidth 32 - (run.add.result.gpr .rax).setWidth 32) at subEq
  rw [run.add.gpr_frame .r14 (by decide), run.add.gpr_frame .rax (by decide)] at subEq
  apply (congrFun run.jump.gpr_frame .r14).trans
  apply subEq.trans
  exact (BitVec.setWidth_eq_append (by decide)).symm

theorem UpdateRun.rip_target {before : State} (run : UpdateRun before) :
    run.result.rip = run.jump.target := run.jump.taken_rip rfl

theorem UpdateRun.gpr_frame {before : State} (run : UpdateRun before) (register : Gpr)
    (notPointer : register ≠ .r13) (notRemaining : register ≠ .r14) :
    run.result.gpr register = before.gpr register :=
  (congrFun run.jump.gpr_frame register).trans
    ((run.subtract.gpr_frame register notRemaining).trans (run.add.gpr_frame register notPointer))

theorem UpdateRun.state_frame {before : State} (run : UpdateRun before) :
    run.result.machine.memory = before.machine.memory ∧
      run.result.machine.obligations = before.machine.obligations :=
  ⟨run.jump.state_frame.1.trans (run.subtract.state_frame.1.trans run.add.state_frame.1),
    run.jump.state_frame.2.trans (run.subtract.state_frame.2.trans run.add.state_frame.2)⟩

/-- The three actual fetch events extend the existing machine history in order. -/
theorem UpdateRun.events_append {before : State} (run : UpdateRun before) :
    ∃ added, run.result.machine.events = before.machine.events ++ added ∧ added.length = 3 := by
  obtain ⟨added, addEvents, _⟩ := run.add.events_exact
  obtain ⟨subtracted, subEvents, _⟩ := run.subtract.events_exact
  obtain ⟨jumped, jumpEvents, _⟩ := run.jump.events_exact
  refine ⟨[added, subtracted, jumped], ?_, rfl⟩
  change run.jump.result.machine.events = _
  rw [jumpEvents, subEvents, addEvents]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem UpdateRun.cursor_advanced {payload : Vec Byte} {base : Nat}
    {cursor : WriteCursor payload} {before : State} (run : UpdateRun before)
    (placed : CursorRegisters payload base cursor before) (count : WriteCount cursor)
    (loaded : (before.gpr .rax).toNat = count.value) :
    CursorRegisters payload base (advance cursor count) run.result := by
  have remainingLength : cursor.remaining.length = payload.length - cursor.committed :=
    Vec.length_drop payload cursor.committed
  have within := count.within
  have cursorWithin := cursor.within
  have countFits := placed.countFits
  have addressFits := placed.addressFits
  have countSmall : count.value < 2 ^ 32 := by omega
  have remainingSmall : (before.gpr .r14).toNat < 2 ^ 32 := by rw [placed.remaining]; omega
  have countLow : ((before.gpr .rax).setWidth 32).toNat = count.value := by
    rw [BitVec.toNat_setWidth, loaded, Nat.mod_eq_of_lt countSmall]
  have remainingLow : ((before.gpr .r14).setWidth 32).toNat = cursor.remaining.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt remainingSmall, placed.remaining]
  refine ⟨?_, ?_, placed.addressFits, placed.countFits⟩
  · rw [run.pointer_exact, BitVec.toNat_add, placed.pointer, loaded]
    change (base + cursor.committed + count.value) % 2 ^ 64 = base + (cursor.committed + count.value)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [run.remaining_exact, BitVec.toNat_setWidth_of_le (by decide)]
    rw [BitVec.toNat_sub_of_not_usubOverflow (by
      simp only [BitVec.usubOverflow, decide_eq_true_eq, Nat.not_lt]
      rw [remainingLow, countLow]
      exact within), remainingLow, countLow]
    simp only [WriteCursor.remaining, Vec.length_drop, advance]
    omega

open Grass.Assembly

/-- Bind the continuous receipt suffix to three consecutive outputs in the
same source and loaded image. No duplicate fetch or numeric target is selected. -/
structure SourceUpdate {frame : SourceFrame.Result} {rootOffset : Nat}
    (source : SourceResolve.Result frame rootOffset) {before : State} (run : UpdateRun before) where
  addSite : SourceFetch.SourceSite source before run.addFetch
  addFetchExact : addSite.fetch = run.add.execution.fetch
  subSite : SourceFetch.SourceSite source run.add.result run.subFetch
  subFetchExact : subSite.fetch = run.subtract.execution.fetch
  jumpSite : SourceFetch.SourceSite source run.subtract.result run.jumpFetch
  jumpFetchExact : jumpSite.fetch = run.jump.execution.fetch
  subIndex : subSite.output.index = addSite.output.index + 1
  jumpIndex : jumpSite.output.index = subSite.output.index + 1
  subImage : subSite.loadedImageBase = addSite.loadedImageBase
  jumpImage : jumpSite.loadedImageBase = addSite.loadedImageBase
  subProvenance : subSite.fetch.descriptor.provenance = addSite.fetch.descriptor.provenance
  jumpProvenance : jumpSite.fetch.descriptor.provenance = addSite.fetch.descriptor.provenance
  subAllocation : subSite.fetch.run.resolved.allocation = addSite.fetch.run.resolved.allocation
  jumpAllocation : jumpSite.fetch.run.resolved.allocation = addSite.fetch.run.resolved.allocation
  subCodeOffset : subSite.codeRootOffset = addSite.codeRootOffset
  jumpCodeOffset : jumpSite.codeRootOffset = addSite.codeRootOffset
  targetIndex : Nat
  resolved : SignedRel32.Resolved
  branchDetail : jumpSite.output.detail = .branch .jump targetIndex resolved
  displacementExact : run.displacement = resolved.bits

theorem SourceUpdate.rip_source_target {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State} {run : UpdateRun before}
    (bound : SourceUpdate source run) :
    run.result.rip = BitVec.ofNat 64 (bound.addSite.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes bound.targetIndex) := by
  have detail := bound.jumpSite.output.detailExact
  rw [bound.branchDetail] at detail
  obtain ⟨_, _, targetEq, resolvedEq, encodingEq⟩ := detail
  have targetMath := SignedRel32.target_equation_of_resolve? resolvedEq
  have sizeEq : bound.jumpSite.fetch.site.encoding.size = Rel32.encodedSize .jump := by
    rw [bound.jumpSite.encoding_exact, encodingEq]
    rfl
  have ripEq := bound.jumpSite.rip_exact
  rw [bound.jumpImage] at ripEq
  have fallthrough : run.jump.execution.fetch.site.fallthroughRip.toNat =
      bound.addSite.loadedImageBase +
        SourceResolve.sourceOffset source.codeBase source.splice.finalSizes bound.jumpSite.output.index +
        Rel32.encodedSize .jump := by
    rw [← bound.jumpFetchExact, DecodedSite.fallthroughRip_toNat, ripEq, sizeEq]
  rw [run.rip_target]
  change BitVec.ofInt 64 _ = _
  rw [fallthrough, bound.displacementExact]
  have sumEq : (Int.ofNat (bound.addSite.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes bound.jumpSite.output.index +
      Rel32.encodedSize .jump) + bound.resolved.bits.toInt) =
      Int.ofNat (bound.addSite.loadedImageBase +
        SourceResolve.sourceOffset source.codeBase source.splice.finalSizes bound.targetIndex) := by
    rw [← targetEq]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add] at targetMath ⊢
    omega
  simp only [BranchInstruction.displacement]
  rw [sumEq]
  rfl

open Grass.Console Grass.Semantics Grass.Op Grass.Platform.Win32.WriteFile
open Grass.Refinement.Console.WriteFileHistory

/-- Compose a successful partial matched return with the actual update suffix.
The caller must supply the real DWORD-load connection into RAX; no load or
resume is manufactured from the logical return. The observed prefix is retained. -/
theorem retry_observed {R Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
    {spec : SpecProcess resources} {projection : CapturedTargetProjection spec Status}
    {realization : Realization} {initial pending after : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {frontier : Prefix pending call record}
    {history : History realization initial call record frontier}
    {relation : HandoffRelation projection} {aligned : Aligned relation history}
    {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : Returned aligned selected result after)
    (success : result.rawBool ≠ 0) (positive : 0 < frontier.accepted)
    (proper : aligned.endpoint.offset < projection.target.payload.length)
    {base : Nat} {before : State} (run : UpdateRun before)
    (placed : CursorRegisters projection.target.payload base returned.cursor before)
    (loaded : (before.gpr .rax).toNat = returned.count.value) :
    CursorRegisters projection.target.payload base (advance returned.cursor returned.count) run.result ∧
      returned.retryObservedHistory (advance returned.cursor returned.count)
        (returned.partial_success_decision success positive proper) = aligned.observedHistory ∧
      (advance returned.cursor returned.count).remaining = aligned.endpoint.remaining :=
  ⟨run.cursor_advanced placed returned.count loaded,
    (returned.retry_observed_exact _ (returned.partial_success_decision success positive proper)).1,
    (returned.retry_observed_exact _ (returned.partial_success_decision success positive proper)).2.2⟩

end Grass.Refinement.Console.WriteAllX86
