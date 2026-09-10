import Grass.ISA.X86.Execution.MemoryMoveFactory
import Grass.Refinement.Console.WriteAllFactory
import Grass.Refinement.Console.WriteAllGuards

/-! The reached positive-count body of the authored write loop. The exact
initialized load and continuous guard/update receipts supply the CPU behavior.
Provider roundtrip, source placement and entry reachability remain upstream.
-/

namespace Grass.Refinement.Console.WriteAllBody

open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Memory Grass.Std.Logical Grass.Std.Console
open Grass.Platform.Win32.WriteFile
open WriteAllX86 WriteFileLoad

/-- Bind the actual memory-MOV load access to its resolved frame occurrence. -/
def sourceLoad {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterData : MachineState} {instruction : MemoryMoveNormal.Instruction}
    {encoded : MemoryMoveNormal.Instruction.Encoding instruction}
    (receipt : MemoryMoveNormal.LoadNormal instruction encoded before afterFetch afterData)
    (selection : SourceResolve.LoadSelection source)
    (site : SourceFetch.SourceSite source before afterFetch)
    (sameFetch : site.fetch = receipt.fetch) (selected : site.output = selection.output)
    (range : receipt.access.descriptor.range = selection.result.address.range)
    (base : MachineAddress) (placed : receipt.access.run.resolved.allocation.base = some base)
    (rsp : before.gpr .rsp = addressOf base selection.result.address.rootOffset) :
    FrameMemoryExecution.LoadNormal source before afterFetch afterData := by
  rcases site with ⟨output, outputAt, fetch, space, observed, codeBase, codePlaced,
    codeOffset, image, placement, start⟩
  dsimp only at sameFetch selected
  subst fetch
  exact
    { selection := selection
      site := ⟨output, outputAt, receipt.fetch, space, observed, codeBase, codePlaced,
        codeOffset, image, placement, start⟩
      selected := selected
      access := receipt.access
      intent := receipt.intent
      initialization := receipt.initialization
      range := range
      base := base
      placed := placed
      rsp := rsp }

theorem sourceLoad_result {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterData : MachineState} {instruction : MemoryMoveNormal.Instruction}
    {encoded : MemoryMoveNormal.Instruction.Encoding instruction}
    (receipt : MemoryMoveNormal.LoadNormal instruction encoded before afterFetch afterData)
    (selection : SourceResolve.LoadSelection source)
    (site : SourceFetch.SourceSite source before afterFetch)
    (sameFetch : site.fetch = receipt.fetch) (selected : site.output = selection.output)
    (range : receipt.access.descriptor.range = selection.result.address.range)
    (base : MachineAddress) (placed : receipt.access.run.resolved.allocation.base = some base)
    (rsp : before.gpr .rsp = addressOf base selection.result.address.rootOffset)
    (instructionSelected : instruction = .load32
      (BitVec.ofNat 32 selection.result.address.displacement) selection.result.destination) :
    (sourceLoad receipt selection site sameFetch selected range base placed rsp).result =
      receipt.result := by
  have destination := (MemoryMoveNormal.Instruction.load32.inj
    (receipt.instructionExact.symm.trans instructionSelected)).2
  rcases site with ⟨output, outputAt, fetch, space, observed, codeBase, codePlaced,
    codeOffset, image, placement, start⟩
  dsimp only at sameFetch selected
  subst fetch
  simp only [sourceLoad, FrameMemoryExecution.LoadNormal.result,
    FrameMemoryExecution.LoadNormal.execution, MemoryMoveNormal.LoadNormal.result,
    MemoryMoveNormal.LoadNormal.read]
  rw [destination]

/-- The selected authored load writes EAX; this is recovered from source syntax. -/
theorem load_operand {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    (selected : WriteAllGuardSource.Selection source)
    (selection : SourceResolve.LoadSelection source)
    (same : selection.output = selected.candidate.load.output) :
    selection.result.destination = .rax ∧ selection.result.slot = "transferred" := by
  have sourceSyntax := selected.valid.2.1
  rw [← same] at sourceSyntax
  unfold WriteAllLoopSource.originInstruction at sourceSyntax
  rw [selection.originExact] at sourceSyntax
  change some selection.item.instruction = some WriteAllGuardSource.loadInstruction at sourceSyntax
  have item := (FrameLoad.resolve?_source selection.success).2.1
  have instruction := selection.result.instructionExact
  rw [item, Option.some.inj sourceSyntax] at instruction
  simp only [WriteAllGuardSource.loadInstruction, X86Source.Instruction.mk.injEq,
    List.cons.injEq, X86Source.Operand.register.injEq,
    X86Source.Register.mk.injEq, X86Source.Operand.symbol.injEq] at instruction
  exact ⟨instruction.2.1.1.symm, instruction.2.2.1.symm⟩

theorem load_destination {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    (selected : WriteAllGuardSource.Selection source)
    (selection : SourceResolve.LoadSelection source)
    (same : selection.output = selected.candidate.load.output) :
    selection.result.destination = .rax := (load_operand selected selection same).1

theorem load_gpr_frame {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterData : MachineState}
    (load : FrameMemoryExecution.LoadNormal source before afterFetch afterData)
    (register : Gpr) (different : register ≠ load.selection.result.destination) :
    load.result.gpr register = before.gpr register := by
  change (if register = load.selection.result.destination then _ else _) = _
  simp only [different, ↓reduceIte]

theorem cursor_after_load_checks {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterData : MachineState}
    (load : FrameMemoryExecution.LoadNormal source before afterFetch afterData)
    (checks : CountChecks load.result)
    (destination : load.selection.result.destination = .rax)
    {payload : Vec Byte} {base : Nat} {cursor : WriteCursor payload}
    (placed : CursorRegisters payload base cursor before) :
    CursorRegisters payload base cursor checks.result := by
  refine ⟨?_, ?_, placed.addressFits, placed.countFits⟩
  · rw [checks.gpr_frame, load_gpr_frame load .r13 (by rw [destination]; decide)]
    exact placed.pointer
  · rw [checks.gpr_frame, load_gpr_frame load .r14 (by rw [destination]; decide)]
    exact placed.remaining

/-- One successful fixed memory-MOV factory call, bound to its exact source
load. The factory equation retains the actual initialized data access. -/
structure FactoryLoad (policy : CpuAccessPolicy) {frame : SourceFrame.Result}
    {rootOffset : Nat} (source : SourceResolve.Result frame rootOffset) (before : State) where
  fetched : FetchFactory.Success policy before
  instruction : MemoryMoveNormal.Instruction
  encoded : MemoryMoveNormal.Instruction.Encoding instruction
  afterData : MachineState
  receipt : MemoryMoveNormal.LoadNormal instruction encoded before fetched.after afterData
  fetchExact : receipt.fetch = fetched.dispatched.fetch
  ran : MemoryMoveFactory.memoryMove policy before =
    .ok ⟨fetched, .load encoded receipt fetchExact⟩
  selection : SourceResolve.LoadSelection source
  site : SourceFetch.SourceSite source before fetched.after
  sameFetch : site.fetch = receipt.fetch
  selected : site.output = selection.output
  range : receipt.access.descriptor.range = selection.result.address.range
  base : MachineAddress
  placed : receipt.access.run.resolved.allocation.base = some base
  rsp : before.gpr .rsp = addressOf base selection.result.address.rootOffset
  instructionSelected : instruction = .load32
    (BitVec.ofNat 32 selection.result.address.displacement) selection.result.destination

@[irreducible] def FactoryLoad.source {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (load : FactoryLoad policy source before) :
    FrameMemoryExecution.LoadNormal source before load.fetched.after load.afterData :=
  sourceLoad load.receipt load.selection load.site load.sameFetch load.selected
    load.range load.base load.placed load.rsp

theorem FactoryLoad.result_exact {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (load : FactoryLoad policy source before) : load.source.result = load.receipt.result := by
  unfold FactoryLoad.source
  exact sourceLoad_result load.receipt load.selection load.site load.sameFetch load.selected
    load.range load.base load.placed load.rsp load.instructionSelected

theorem FactoryLoad.actual_result {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (load : FactoryLoad policy source before) :
    ∃ success, MemoryMoveFactory.memoryMove policy before = .ok success ∧
      success.execution.result = load.source.result :=
  ⟨⟨load.fetched, .load load.encoded load.receipt load.fetchExact⟩,
    load.ran, load.result_exact.symm⟩

theorem FactoryLoad.descriptor_exact {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (load : FactoryLoad policy source before) :
    load.source.access.descriptor = load.receipt.access.descriptor := by
  rcases load with ⟨fetched, instruction, encoded, afterData, receipt, fetchExact, ran,
    selection, site, sameFetch, selected, range, base, placed, rsp, instructionSelected⟩
  rcases site with ⟨output, outputAt, fetch, space, observed, codeBase, codePlaced,
    codeOffset, image, placement, start⟩
  dsimp only at sameFetch
  subst fetch
  unfold FactoryLoad.source
  rfl

/-- Continuous load, TEST/JZ/CMP/JA and ADD/SUB/JMP, all bound to the same
selected authored body and loaded code region. -/
structure Run (policy : CpuAccessPolicy) {frame : SourceFrame.Result} {rootOffset : Nat}
    (source : SourceResolve.Result frame rootOffset) (before : State) where
  load : FactoryLoad policy source before
  checks : CountChecks load.source.result
  update : UpdateRun checks.result
  selected : WriteAllGuardSource.Selection source
  checksSource : SourceChecks selected load.source checks
  updateSource : SourceUpdate source update
  authored : AuthoredUpdate selected.candidate.loop updateSource
  addCode : SameCodeSite load.source.site update.add.execution.fetch
  addSite : addCode.site = updateSource.addSite

/-- A positive initialized count within the retained cursor passes both actual
count guards and reestablishes the cursor at the authored head. No free read
value or full-register width equation is assumed. -/
theorem Run.reenters_head {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (run : Run policy source before) {payload : Vec Byte} {base : Nat}
    {cursor : WriteCursor payload} (placed : CursorRegisters payload base cursor before)
    (argument : Argument) (value : BitVec 32)
    (observed : DwordAt before.machine.memory argument value)
    (provenance : run.load.source.access.descriptor.provenance = argument.provenance)
    (range : run.load.source.access.descriptor.range = argument.range)
    (bounded : value.toNat ≤ cursor.remaining.length) (positive : 0 < value.toNat) :
    run.checks.zeroBranch.result.rip =
        run.checks.zeroBranch.execution.fetch.site.fallthroughRip ∧
    run.checks.aboveBranch.result.rip =
        run.checks.aboveBranch.execution.fetch.site.fallthroughRip ∧
    CursorRegisters payload base (advance cursor ⟨value.toNat, bounded⟩) run.update.result ∧
    run.update.result.gpr .r12 = before.gpr .r12 ∧
    run.update.result.gpr .rsp = before.gpr .rsp ∧
    run.update.result.rip = BitVec.ofNat 64 (run.load.source.site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes
        run.selected.candidate.loop.candidate.headIndex) ∧
    run.update.result.machine.memory = before.machine.memory := by
  have destination : run.load.source.selection.result.destination = .rax :=
    load_destination run.selected run.load.source.selection
      (run.load.source.selected.symm.trans run.checksSource.loadSelected)
  have loaded := load_value run.load.source argument value observed provenance range
  rw [destination] at loaded
  have lowLoaded : ((run.load.source.result.gpr .rax).setWidth 32).toNat = value.toNat := by
    rw [BitVec.toNat_setWidth, loaded, Nat.mod_eq_of_lt value.isLt]
  have remainingSmall : cursor.remaining.length < 2 ^ 32 := by
    have fits := placed.countFits
    simp only [WriteCursor.remaining, Vec.length_drop] at *
    omega
  have remaining : ((run.load.source.result.gpr .r14).setWidth 32).toNat =
      cursor.remaining.length := by
    rw [load_gpr_frame run.load.source .r14 (by rw [destination]; decide),
      BitVec.toNat_setWidth, placed.remaining, Nat.mod_eq_of_lt remainingSmall]
  have zeroFalls := run.checks.positive_fallthrough (by rw [lowLoaded]; exact positive)
  have aboveFalls := run.checks.bounded_fallthrough (by rw [lowLoaded, remaining]; exact bounded)
  have cursorPlaced := cursor_after_load_checks run.load.source run.checks destination placed
  have finalLoaded := checked_load_value run.load.source run.checks argument value observed
    provenance range destination
  have closed := run.authored.reenters_head cursorPlaced ⟨value.toNat, bounded⟩ finalLoaded
  have image : run.updateSource.addSite.loadedImageBase = run.load.source.site.loadedImageBase := by
    rw [← run.addSite]
    exact run.addCode.image
  rw [image] at closed
  refine ⟨zeroFalls, aboveFalls, closed.1, ?_, ?_, closed.2.2, ?_⟩
  · rw [closed.2.1, run.checks.gpr_frame,
      load_gpr_frame run.load.source .r12 (by rw [destination]; decide)]
  · rw [run.update.gpr_frame .rsp (by decide) (by decide), run.checks.gpr_frame,
      load_gpr_frame run.load.source .rsp (by rw [destination]; decide)]
  · exact run.update.state_frame.1.trans
      (run.checks.memory_frame.trans run.load.source.memory_frame)

/-- The same body consumes the count justified by the exact matched provider
history. The physical resume remains upstream: its retained post-return memory
must be the actual pre-load memory, and the reached cursor must be supplied. -/
theorem Run.returned_reenters_head
    {R Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
    {spec : Grass.SpecProcess resources}
    {projection : Grass.Console.CapturedTargetProjection spec Status}
    {plan : LoanPlan} {realization : Realization}
    {initial providerBefore after : ProtocolState}
    {call : Grass.Op.CallProtocol.CallId} {record : Grass.Op.CallProtocol.Pending Request}
    {frontier : Prefix plan providerBefore call record}
    {history : History plan realization initial call record frontier}
    {relation : WriteFileHistory.HandoffRelation (plan := plan) projection}
    {aligned : WriteFileHistory.Aligned relation history}
    {interpretation : ReturnInterpretation} {result : ReturnResult}
    (returned : WriteFileHistory.Returned aligned interpretation result after)
    {policy : CpuAccessPolicy} {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    (run : Run policy source before) {base : Nat}
    (placed : CursorRegisters projection.target.payload base returned.cursor before)
    (resumedMemory : before.machine.memory = after.machine.memory)
    (success : result.rawBool ≠ 0) (positive : 0 < returned.count.value)
    (provenance : run.load.source.access.descriptor.provenance = record.request.countSlot.provenance)
    (range : run.load.source.access.descriptor.range = record.request.countSlot.range) :
    CursorRegisters projection.target.payload base (advance returned.cursor returned.count)
      run.update.result ∧
    run.update.result.rip = BitVec.ofNat 64 (run.load.source.site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes
        run.selected.candidate.loop.candidate.headIndex) ∧
    run.update.result.machine.memory = after.machine.memory := by
  obtain ⟨value, _reported, observed, accepted, _bounded⟩ :=
    returned.matched.conforms_after.success success
  have observedBefore : DwordAt before.machine.memory record.request.countSlot value := by
    rw [resumedMemory]
    exact observed
  have countExact : value.toNat = returned.count.value := accepted
  have bounded : value.toNat ≤ returned.cursor.remaining.length := by
    rw [countExact]
    exact returned.count.within
  have closed := run.reenters_head placed record.request.countSlot value observedBefore provenance
    range bounded (by rw [countExact]; exact positive)
  have sameCount : (⟨value.toNat, bounded⟩ : WriteCount returned.cursor) = returned.count := by
    change (⟨value.toNat, bounded⟩ : WriteCount returned.cursor) = ⟨frontier.accepted, _⟩
    congr 1
  rw [sameCount] at closed
  exact ⟨closed.2.2.1, closed.2.2.2.2.2.1, closed.2.2.2.2.2.2.trans resumedMemory⟩

end Grass.Refinement.Console.WriteAllBody
