import Grass.Refinement.Console.WriteFileLoad
import Grass.Assembly.WriteAllGuardSource

/-! Source correspondence for actual post-load guard receipts. No new machine
transition is selected here; source sites identify the already retained fetches.
-/

namespace Grass.Refinement.Console.WriteFileLoad

open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Memory

theorem source_branch_target {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterCompute : MachineState} {instruction : BranchInstruction}
    (branch : BranchNormal before afterFetch afterCompute instruction)
    (site : SourceFetch.SourceSite source before afterFetch)
    (sameFetch : site.fetch = branch.execution.fetch) (targetIndex : Nat)
    (selected : WriteAllGuardSource.branchTargetFor instruction.kind site.output = some targetIndex) :
    branch.target = BitVec.ofNat 64 (site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes targetIndex) := by
  obtain ⟨resolved, detailEq⟩ : ∃ resolved,
      site.output.detail = .branch instruction.kind targetIndex resolved := by
    cases detailEq : site.output.detail <;>
      simp only [WriteAllGuardSource.branchTargetFor, detailEq] at selected
    all_goals try contradiction
    split at selected
    · rename_i actual target resolved kindEq
      cases kindEq
      cases Option.some.inj selected
      exact ⟨resolved, rfl⟩
    · contradiction
  have detail := site.output.detailExact
  rw [detailEq] at detail
  obtain ⟨_, _, targetEq, resolvedEq, encodingEq⟩ := detail
  have encoding : instruction.encoding = Rel32.encode instruction.kind resolved.bits :=
    branch.encoding.symm.trans ((congrArg (fun fetch => fetch.site.encoding) sameFetch).symm.trans
      (site.encoding_exact.trans encodingEq))
  have bits : instruction.displacement = resolved.bits := by
    have immediate := congrArg InsnEncoding.imm encoding
    exact Immediate.i32.inj immediate
  have fallthrough : branch.execution.fetch.site.fallthroughRip.toNat =
      site.loadedImageBase + SourceResolve.sourceOffset source.codeBase source.splice.finalSizes site.output.index +
        Rel32.encodedSize instruction.kind := by
    rw [← sameFetch, DecodedSite.fallthroughRip_toNat, site.rip_exact,
      site.encoding_exact, encodingEq, Rel32.size_eq]
  have targetMath := SignedRel32.target_equation_of_resolve? resolvedEq
  have sumEq : Int.ofNat (site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes site.output.index +
      Rel32.encodedSize instruction.kind) + resolved.bits.toInt =
      Int.ofNat (site.loadedImageBase + SourceResolve.sourceOffset source.codeBase source.splice.finalSizes targetIndex) := by
    rw [← targetEq]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add] at targetMath ⊢
    omega
  unfold BranchNormal.target
  rw [fallthrough, bits, sumEq]
  rfl

/-- Shared loaded-code identity for one of the actual guard fetches. -/
structure SameCodeSite {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {anchorBefore before : State}
    {anchorAfter afterFetch : MachineState}
    (anchor : SourceFetch.SourceSite source anchorBefore anchorAfter)
    (fetch : FetchedSite before afterFetch) where
  site : SourceFetch.SourceSite source before afterFetch
  fetchExact : site.fetch = fetch
  provenance : site.fetch.descriptor.provenance = anchor.fetch.descriptor.provenance
  allocation : site.fetch.run.resolved.allocation = anchor.fetch.run.resolved.allocation
  codeOffset : site.codeRootOffset = anchor.codeRootOffset
  image : site.loadedImageBase = anchor.loadedImageBase

/-- Every guard is the exact next authored occurrence after this actual load,
and every receipt fetch shares the load's code region and image identity. -/
structure SourceChecks {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    (selected : WriteAllGuardSource.Selection source) {before : State}
    {afterFetch afterLoad : MachineState}
    (load : FrameMemoryExecution.LoadNormal source before afterFetch afterLoad)
    (checks : CountChecks load.result) where
  loadSelected : load.site.output = selected.candidate.load.output
  tested : SameCodeSite load.site checks.tested.execution.fetch
  testSelected : tested.site.output = selected.candidate.tested.output
  zero : SameCodeSite load.site checks.zeroBranch.execution.fetch
  zeroSelected : zero.site.output = selected.candidate.zero.output
  compared : SameCodeSite load.site checks.compared.execution.fetch
  cmpSelected : compared.site.output = selected.candidate.compared.output
  above : SameCodeSite load.site checks.aboveBranch.execution.fetch
  aboveSelected : above.site.output = selected.candidate.above.output

theorem SourceChecks.zero_target {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {selected : WriteAllGuardSource.Selection source}
    {before : State} {afterFetch afterLoad : MachineState}
    {load : FrameMemoryExecution.LoadNormal source before afterFetch afterLoad} {checks : CountChecks load.result}
    (bound : SourceChecks selected load checks) :
    checks.zeroBranch.target = BitVec.ofNat 64 (load.site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.zeroTarget) := by
  rw [source_branch_target checks.zeroBranch bound.zero.site bound.zero.fetchExact
    selected.candidate.zeroTarget (by
      rw [bound.zeroSelected]
      exact selected.valid.2.2.2.2.2.2.2.2.1), bound.zero.image]

theorem SourceChecks.above_target {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {selected : WriteAllGuardSource.Selection source}
    {before : State} {afterFetch afterLoad : MachineState}
    {load : FrameMemoryExecution.LoadNormal source before afterFetch afterLoad} {checks : CountChecks load.result}
    (bound : SourceChecks selected load checks) :
    checks.aboveBranch.target = BitVec.ofNat 64 (load.site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.aboveTarget) := by
  rw [source_branch_target checks.aboveBranch bound.above.site bound.above.fetchExact
    selected.candidate.aboveTarget (by
      rw [bound.aboveSelected]
      exact selected.valid.2.2.2.2.2.2.2.2.2), bound.above.image]

/-- One continuous TEST r32,r32 followed by its actual equal branch. -/
structure TestZeroRun (register : Gpr) (before : State) where
  testFetch : MachineState
  testCompute : MachineState
  tested : ArithmeticNormal before testFetch testCompute (.test .w32 register register)
  branchFetch : MachineState
  branchCompute : MachineState
  displacement : BitVec 32
  branch : BranchNormal tested.result branchFetch branchCompute (.equal displacement)

def TestZeroRun.result {register : Gpr} {before : State} (run : TestZeroRun register before) : State :=
  run.branch.result

theorem TestZeroRun.zero_flag {register : Gpr} {before : State} (run : TestZeroRun register before) :
    run.tested.result.statusFlags.zf = ((before.gpr register).setWidth 32 == 0) := by
  have zero := run.tested.flags_conform.2.2.2.1
  change (some (((before.gpr register).setWidth 32 &&& (before.gpr register).setWidth 32) == 0) = none ∨
    some (((before.gpr register).setWidth 32 &&& (before.gpr register).setWidth 32) == 0) =
      some run.tested.result.statusFlags.zf) at zero
  have equation : ((before.gpr register).setWidth 32 == 0) = run.tested.result.statusFlags.zf := by
    simpa only [BitVec.and_self, reduceCtorEq, false_or, Option.some.injEq] using zero
  exact equation.symm

/-- Source binding for one guard, available without any later load or check
receipt. In particular, failure and head-success need not reach a DWORD read. -/
structure SourceGuard {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    (testOutput branchOutput : SourceResolve.Output source.splice source.symbols source.codeBase)
    {register : Gpr} {before : State} (run : TestZeroRun register before) where
  tested : SourceFetch.SourceSite source before run.testFetch
  testFetchExact : tested.fetch = run.tested.execution.fetch
  testSelected : tested.output = testOutput
  branched : SameCodeSite tested run.branch.execution.fetch
  branchSelected : branched.site.output = branchOutput

theorem source_failure_target {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (selected : WriteAllGuardSource.AllSelection source)
    {before : State} {raw : TestZeroRun .rax before}
    (bound : SourceGuard selected.candidate.rawTest.output selected.candidate.failed.output raw) :
    raw.branch.target = BitVec.ofNat 64 (bound.tested.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.failureTarget) := by
  rw [source_branch_target raw.branch bound.branched.site bound.branched.fetchExact
    selected.candidate.failureTarget (by
      rw [bound.branchSelected]
      exact selected.valid.2.2.2.2.2.2.2), bound.branched.image]

theorem source_success_target {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (selected : WriteAllGuardSource.AllSelection source)
    {before : State} {head : TestZeroRun .r14 before}
    (bound : SourceGuard selected.candidate.post.candidate.loop.candidate.head.output
      selected.candidate.headExit.output head) :
    head.branch.target = BitVec.ofNat 64 (bound.tested.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.successTarget) := by
  rw [source_branch_target head.branch bound.branched.site bound.branched.fetchExact
    selected.candidate.successTarget (by
      rw [bound.branchSelected]
      exact selected.valid.2.2.2.2.2.2.1), bound.branched.image]

/-- Source bindings along a path that reaches the load. The raw-BOOL branch result is
the actual load's input state, and all fetches share that load's code identity.
This does not assert that a zero-BOOL path reaches the load. -/
structure SourceGuards {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    (selected : WriteAllGuardSource.AllSelection source) {headBefore resumed : State}
    (head : TestZeroRun .r14 headBefore) (raw : TestZeroRun .rax resumed)
    {afterFetch afterLoad : MachineState}
    (load : FrameMemoryExecution.LoadNormal source raw.result afterFetch afterLoad)
    (checks : CountChecks load.result) where
  headTest : SameCodeSite load.site head.tested.execution.fetch
  headSelected : headTest.site.output = selected.candidate.post.candidate.loop.candidate.head.output
  headBranch : SameCodeSite load.site head.branch.execution.fetch
  headExitSelected : headBranch.site.output = selected.candidate.headExit.output
  rawTest : SameCodeSite load.site raw.tested.execution.fetch
  rawSelected : rawTest.site.output = selected.candidate.rawTest.output
  rawBranch : SameCodeSite load.site raw.branch.execution.fetch
  failedSelected : rawBranch.site.output = selected.candidate.failed.output
  post : SourceChecks selected.candidate.post load checks

theorem SourceGuards.head_target {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {selected : WriteAllGuardSource.AllSelection source}
    {headBefore resumed : State} {head : TestZeroRun .r14 headBefore} {raw : TestZeroRun .rax resumed}
    {afterFetch afterLoad : MachineState}
    {load : FrameMemoryExecution.LoadNormal source raw.result afterFetch afterLoad} {checks : CountChecks load.result}
    (bound : SourceGuards selected head raw load checks) :
    head.branch.target = BitVec.ofNat 64 (load.site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.successTarget) := by
  rw [source_branch_target head.branch bound.headBranch.site bound.headBranch.fetchExact
    selected.candidate.successTarget (by
      rw [bound.headExitSelected]
      exact selected.valid.2.2.2.2.2.2.1), bound.headBranch.image]

theorem SourceGuards.failure_target {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {selected : WriteAllGuardSource.AllSelection source}
    {headBefore resumed : State} {head : TestZeroRun .r14 headBefore} {raw : TestZeroRun .rax resumed}
    {afterFetch afterLoad : MachineState}
    {load : FrameMemoryExecution.LoadNormal source raw.result afterFetch afterLoad} {checks : CountChecks load.result}
    (bound : SourceGuards selected head raw load checks) :
    raw.branch.target = BitVec.ofNat 64 (load.site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.failureTarget) := by
  rw [source_branch_target raw.branch bound.rawBranch.site bound.rawBranch.fetchExact
    selected.candidate.failureTarget (by
      rw [bound.failedSelected]
      exact selected.valid.2.2.2.2.2.2.2), bound.rawBranch.image]

end Grass.Refinement.Console.WriteFileLoad
