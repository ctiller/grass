import Grass.Assembly.SourceFetchPolicy
import Grass.Assembly.LoadedFetchObservation
import Grass.ISA.X86.Execution.CheckedStep

/-! Source-bound branch correspondence for actual checked transitions.
Current code provenance and cells are inputs; successful fetch is not an
assumption. Failed and uncovered alternatives remain explicit. This module
does not establish enabledness, physical fault delivery, or a program VC. -/

namespace Grass.Assembly.SourceBranchExecution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

private theorem branch_fetch {policy : CpuAccessPolicy} {before : State}
    {fetched : FetchFactory.Success policy before} {instruction : BranchInstruction}
    (selected : fetched.dispatched.selection.instruction = .branch instruction)
    {success : BodyComputationFactory.BranchSuccess policy before}
    (ran : BodyComputationFactory.branchFromFetched before fetched = .ok success) :
    success.fetched = fetched ∧ success.instruction = instruction := by
  unfold BodyComputationFactory.branchFromFetched at ran
  dsimp only at ran
  split at ran
  · simp_all only [Instruction.branch.injEq]
    split at ran
    · split at ran
      · contradiction
      · cases ran
        simp_all
    · contradiction
  · simp_all

/-- An actual successful fetch at this source position observes the source
encoding from the current preserved loaded code, without a supplied byte equality. -/
theorem fetched_encoding {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {before : State}
    (contains : ContainsCodeAddress (SourceLoadedImage.codeRegion binding loaded).region before.rip)
    {policy : CpuAccessPolicy} (selected : Cpu.policy? loaded before = some policy)
    (fetched : FetchFactory.Success policy before)
    (present : before.machine.memory.allocations.lookup
      (SourceLoadedImage.codeRegion binding loaded).region.allocId =
      some (SourceLoadedImage.codeRegion binding loaded).region.allocationRecord)
    (index : Nat) (bounded : index < source.outputs.length)
    (rip : before.rip.toNat = (SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
      ByteLayout.offset source.splice.finalSizes index)
    (cells : ∀ offset, before.machine.memory.cellAt?
      (SourceLoadedImage.codeRegion binding loaded).region.allocId offset =
      loaded.initialState.machine.memory.cellAt?
        (SourceLoadedImage.codeRegion binding loaded).region.allocId offset)
    (outside : ∀ i, i < source.outputs[index].encoding.size → ∀ patch ∈ loaded.patches,
      ¬ (patch.rva ≤ source.codeBase + ByteLayout.offset source.splice.finalSizes index + i ∧
        source.codeBase + ByteLayout.offset source.splice.finalSizes index + i < patch.rva + 8)) :
    fetched.dispatched.fetch.site.encoding = source.outputs[index].encoding := by
  have start := SourceFetchPolicy.fetched_source_start binding loaded contains selected fetched present index rip
  have width := SourceFetchPolicy.fetched_source_width binding loaded contains selected fetched present
    index bounded rip cells outside
  have root := SourceFetchPolicy.fetched_code_root binding loaded contains selected fetched
  have observed := LoadedFetchObservation.observed_source binding loaded index bounded
    fetched.dispatched.fetch (fun offset _ => cells offset) root start width (by
      intro offset covered patch member
      have bounds := covered
      simp only [ByteRange.covers_def] at bounds
      have localBound : offset - ByteLayout.offset source.splice.finalSizes index <
          source.outputs[index].encoding.size := by omega
      have excluded := outside (offset - ByteLayout.offset source.splice.finalSizes index)
        localBound patch member
      have coordinates : source.codeBase + ByteLayout.offset source.splice.finalSizes index +
          (offset - ByteLayout.offset source.splice.finalSizes index) = source.codeBase + offset := by omega
      rwa [coordinates] at excluded)
  exact fetched.dispatched.fetch.encoding_of_observation source.outputs[index].encoding
    (by simpa using source.outputs[index].encodingDecodes []) observed

private theorem failure_outside {failure : CheckedExecution.Failure} {outcome : CpuOutcome}
    (mapped : failure.outcome = some outcome) :
    ∃ reached reason, outcome = .outsideProfile reached reason := by
  cases failure with
  | fetch reason => cases reason <;> cases mapped <;> exact ⟨_, _, rfl⟩
  | computation reason =>
    cases reason with
    | fetch reason => cases reason <;> cases mapped <;> exact ⟨_, _, rfl⟩
    | unsupported | accessFreeRejected => cases mapped; exact ⟨_, _, rfl⟩
  | body reason =>
    cases reason with
    | fetch reason => cases reason <;> cases mapped <;> exact ⟨_, _, rfl⟩
    | flagsRejected => contradiction
    | unsupported | accessFreeRejected | targetOutOfRange => cases mapped; exact ⟨_, _, rfl⟩
  | push reason =>
    cases reason with
    | fetch reason => cases reason <;> cases mapped <;> exact ⟨_, _, rfl⟩
    | unsupported | stackUnderflow | stackAddress | store => cases mapped; exact ⟨_, _, rfl⟩
  | call reason =>
    cases reason with
    | fetch reason => cases reason <;> cases mapped <;> exact ⟨_, _, rfl⟩
    | unsupported | missingData | dataAddress | read | stackUnderflow |
        stackAddress | store => cases mapped; exact ⟨_, _, rfl⟩
  | memoryMove reason =>
    cases reason with
    | fetch reason => cases reason <;> cases mapped <;> exact ⟨_, _, rfl⟩
    | unsupported | address | access => cases mapped; exact ⟨_, _, rfl⟩
  | unsupported => cases mapped; exact ⟨_, _, rfl⟩

private theorem checked_branch_cases {policy : CpuAccessPolicy} {before : State}
    {instruction : BranchInstruction}
    (selects : ∀ fetched : FetchFactory.Success policy before,
      FetchFactory.fetch policy before = .ok fetched →
      fetched.dispatched.selection.instruction = .branch instruction)
    {choice : CheckedChoice} {outcome : CpuOutcome}
    (step : CheckedExecution.CheckedStep policy before choice outcome) :
    (∃ (flags : RegisterSemantics.Flags Bool) (fetched : FetchFactory.Success policy before)
      (success : BodyComputationFactory.BranchSuccess policy before),
      choice = .normal flags ∧ FetchFactory.fetch policy before = .ok fetched ∧
      BodyComputationFactory.branchFromFetched before fetched = .ok success ∧
      outcome = .progressed success.result .completed ∧
      success.fetched = fetched ∧ success.instruction = instruction) ∨
    ∃ reached reason, outcome = .outsideProfile reached reason := by
  cases choice with
  | normal flags =>
    obtain ⟨result, evaluated, mapped⟩ := CheckedExecution.normal_checked_cases step
    cases result with
    | error failure => exact Or.inr (failure_outside mapped)
    | ok success =>
      cases fetchedExact : FetchFactory.fetch policy before with
      | error failure => simp [CheckedExecution.normal, fetchedExact] at evaluated
      | ok fetched =>
        have selected := selects fetched fetchedExact
        simp only [CheckedExecution.normal, fetchedExact, selected] at evaluated
        cases ran : BodyComputationFactory.branchFromFetched before fetched with
        | error failure => simp [ran, Except.map, Except.mapError] at evaluated
        | ok branch =>
          simp only [ran, Except.map, Except.mapError, Option.some.injEq, Except.ok.injEq] at evaluated
          cases evaluated
          exact Or.inl ⟨flags, fetched, branch, rfl, rfl, ran,
            (Option.some.inj mapped).symm, branch_fetch selected ran⟩
  | fault class_ => exact Or.inr ⟨before, .faultTransfer class_, (Option.some.inj step).symm⟩
  | trap class_ => exact Or.inr ⟨before, .trapTransfer class_, (Option.some.inj step).symm⟩
  | interruption vector => exact Or.inr ⟨before, .interruptionTransfer vector, (Option.some.inj step).symm⟩
  | abort class_ => exact Or.inr ⟨before, .abortTransfer class_, (Option.some.inj step).symm⟩

/-- A source-resolved branch receipt lands at the resolved target or its exact
fallthrough according to the actual incoming flags. No program labels or
register allocation are recognized. -/
theorem branch_successor {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} (index : Nat)
    (bounded : index < source.outputs.length)
    {kind : Rel32.Kind} {target : Nat} {resolved : SignedRel32.Resolved}
    (detail : source.outputs[index].detail = .branch kind target resolved)
    {before : State} {afterFetch afterCompute : MachineState} {instruction : BranchInstruction}
    (receipt : BranchNormal before afterFetch afterCompute instruction)
    (encoding : receipt.execution.fetch.site.encoding = source.outputs[index].encoding)
    (bits : instruction.displacement = resolved.bits)
    (base : Nat) (rip : before.rip.toNat = base + ByteLayout.offset source.splice.finalSizes index) :
    receipt.result.rip = if instruction.taken before.statusFlags then
      BitVec.ofNat 64 (base + ByteLayout.offset source.splice.finalSizes target)
      else BitVec.ofNat 64 (base + ByteLayout.offset source.splice.finalSizes index + Rel32.encodedSize kind) := by
  have valid := source.outputs[index].detailExact
  rw [detail] at valid
  obtain ⟨_, _, targetExact, resolvedExact, encodingExact⟩ := valid
  have indexExact : source.outputs[index].index = index := by
    have indices := congrArg (fun indices : List Nat => indices[index]?) source.output_indices
    simpa [List.getElem?_map, List.getElem?_eq_getElem bounded,
      List.getElem?_range, ← source.output_count, bounded] using indices
  have equation := SignedRel32.target_equation_of_resolve? resolvedExact
  rw [targetExact, indexExact] at equation
  simp only [SourceResolve.sourceOffset, Int.natCast_add] at equation
  have fallthrough : receipt.execution.fetch.site.fallthroughRip.toNat =
      base + ByteLayout.offset source.splice.finalSizes index + Rel32.encodedSize kind := by
    rw [DecodedSite.fallthroughRip_toNat, rip, encoding, encodingExact, Rel32.size_eq]
  have targetAddress : receipt.target = BitVec.ofNat 64
      (base + ByteLayout.offset source.splice.finalSizes target) := by
    unfold BranchNormal.target
    rw [fallthrough, bits]
    have translated : Int.ofNat (base + ByteLayout.offset source.splice.finalSizes index +
        Rel32.encodedSize kind) + resolved.bits.toInt =
        Int.ofNat (base + ByteLayout.offset source.splice.finalSizes target) := by
      simp only [Int.ofNat_eq_natCast, Int.natCast_add]
      omega
    rw [translated]
    rfl
  have fallthroughAddress : receipt.execution.fetch.site.fallthroughRip = BitVec.ofNat 64
      (base + ByteLayout.offset source.splice.finalSizes index + Rel32.encodedSize kind) := by
    rw [← fallthrough]
    simp
  simp only [BranchNormal.result, targetAddress, fallthroughAddress]

/-- Every admitted checked outcome at a source-resolved branch is either its
actual branch completion or an explicitly retained outside-profile outcome.
Selection is derived from source evidence; no successful fetch is assumed. -/
theorem sourceBranch_checked_cases {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {before : State}
    (contains : ContainsCodeAddress (SourceLoadedImage.codeRegion binding loaded).region before.rip)
    {policy : CpuAccessPolicy} (selected : Cpu.policy? loaded before = some policy)
    (present : before.machine.memory.allocations.lookup
      (SourceLoadedImage.codeRegion binding loaded).region.allocId =
      some (SourceLoadedImage.codeRegion binding loaded).region.allocationRecord)
    (index : Nat) (bounded : index < source.outputs.length)
    (rip : before.rip.toNat = (SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
      ByteLayout.offset source.splice.finalSizes index)
    (cells : ∀ offset, before.machine.memory.cellAt?
      (SourceLoadedImage.codeRegion binding loaded).region.allocId offset =
      loaded.initialState.machine.memory.cellAt?
        (SourceLoadedImage.codeRegion binding loaded).region.allocId offset)
    (outside : ∀ i, i < source.outputs[index].encoding.size → ∀ patch ∈ loaded.patches,
      ¬ (patch.rva ≤ source.codeBase + ByteLayout.offset source.splice.finalSizes index + i ∧
        source.codeBase + ByteLayout.offset source.splice.finalSizes index + i < patch.rva + 8))
    {kind : Rel32.Kind} {target : Nat} {resolved : SignedRel32.Resolved}
    (detail : source.outputs[index].detail = .branch kind target resolved)
    {choice : CheckedChoice} {outcome : CpuOutcome}
    (step : CheckedExecution.CheckedStep policy before choice outcome) :
    (∃ (flags : RegisterSemantics.Flags Bool)
      (success : BodyComputationFactory.BranchSuccess policy before),
      choice = .normal flags ∧ outcome = .progressed success.result .completed ∧
      FetchFactory.fetch policy before = .ok success.fetched ∧
      success.receipt.execution.fetch.site.encoding = source.outputs[index].encoding ∧
      success.instruction.kind = kind ∧ success.instruction.displacement = resolved.bits ∧
      success.result.gpr = before.gpr ∧
      success.result.rip = if success.instruction.taken before.statusFlags then
        BitVec.ofNat 64 ((SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
          ByteLayout.offset source.splice.finalSizes target)
        else BitVec.ofNat 64 ((SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
          ByteLayout.offset source.splice.finalSizes index + Rel32.encodedSize kind)) ∨
    ∃ reached reason, outcome = .outsideProfile reached reason := by
  let instruction : BranchInstruction := match kind with
    | .jump => .jump resolved.bits
    | .equal => .equal resolved.bits
    | .above => .above resolved.bits
  have kindExact : instruction.kind = kind := by cases kind <;> rfl
  have bitsExact : instruction.displacement = resolved.bits := by cases kind <;> rfl
  have valid := source.outputs[index].detailExact
  rw [detail] at valid
  have encodingExact : source.outputs[index].encoding = instruction.encoding := by
    obtain ⟨_, _, _, _, encoding⟩ := valid
    rw [encoding]
    cases kind <;> rfl
  have classified : (Instruction.select source.outputs[index].encoding).map (·.instruction) =
      some (.branch instruction) := by
    rw [encodingExact]
    exact Instruction.select_branch_complete instruction
  have selects : ∀ fetched : FetchFactory.Success policy before,
      FetchFactory.fetch policy before = .ok fetched →
      fetched.dispatched.selection.instruction = .branch instruction := by
    intro fetched _
    have encoding := fetched_encoding binding loaded contains selected fetched present index bounded rip cells outside
    have actual := congrArg (Option.map (fun selection => selection.instruction)) fetched.dispatched.selected
    have translated := congrArg (fun encoding => (Instruction.select encoding).map (·.instruction)) encoding
    exact Option.some.inj (actual.symm.trans (translated.trans classified))
  rcases checked_branch_cases selects step with ⟨flags, fetched, success, choiceExact, fetchedExact,
      ran, outcomeExact, sameFetch, sameInstruction⟩ | failed
  · have encoding := fetched_encoding binding loaded contains selected fetched present index bounded rip cells outside
    have receiptEncoding : success.receipt.execution.fetch.site.encoding = source.outputs[index].encoding :=
      (congrArg (fun fetch => fetch.site.encoding) success.fetch_exact).trans
        ((congrArg (fun actual : FetchFactory.Success policy before => actual.dispatched.fetch.site.encoding)
          sameFetch).trans encoding)
    have kinds := (congrArg BranchInstruction.kind sameInstruction).trans kindExact
    have bits := (congrArg BranchInstruction.displacement sameInstruction).trans bitsExact
    refine Or.inl ⟨flags, success, choiceExact, outcomeExact, ?_, receiptEncoding, kinds, bits,
      success.receipt.gpr_frame, ?_⟩
    · exact fetchedExact.trans (congrArg Except.ok sameFetch.symm)
    · exact branch_successor index bounded detail success.receipt receiptEncoding bits
        (SourceLoadedImage.codeRegion binding loaded).region.base.toNat rip
  · exact Or.inr failed

end Grass.Assembly.SourceBranchExecution
