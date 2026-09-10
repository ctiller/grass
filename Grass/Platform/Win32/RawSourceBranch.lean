import Grass.Assembly.SourceBranchExecution
import Grass.Platform.Win32.RawStep

/-! Source branch correspondence for an existing raw CPU edge. This retains the
actual event/graph agreement and exact installed state, including outside-profile
outcomes. It does not establish enabledness or whole-execution correspondence. -/

namespace Grass.Platform.Win32.Raw.RawStep
open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Assembly
open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Platform.Win32.Loader
open Grass.Platform.Win32.ExecutionState

/-- The actual raw edge installs the checked source-branch outcome, with original
choice, event and graph obligations retained. -/
theorem cpu_branch_successor {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {before after : RawState}
    {graph nextGraph : Graph} {event : Event}
    {realization : WriteFile.Realization} {environment : ConsoleEnvironment}
    {interpretation : WriteFile.ReturnInterpretation}
    (contains : ContainsCodeAddress (SourceLoadedImage.codeRegion binding loaded).region before.machine.rip)
    (present : before.machine.machine.memory.allocations.lookup
      (SourceLoadedImage.codeRegion binding loaded).region.allocId =
      some (SourceLoadedImage.codeRegion binding loaded).region.allocationRecord)
    (index : Nat) (bounded : index < source.outputs.length)
    (rip : before.machine.rip.toNat = (SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
      ByteLayout.offset source.splice.finalSizes index)
    (cells : ∀ offset, before.machine.machine.memory.cellAt?
      (SourceLoadedImage.codeRegion binding loaded).region.allocId offset =
      loaded.initialState.machine.memory.cellAt?
        (SourceLoadedImage.codeRegion binding loaded).region.allocId offset)
    (outside : ∀ i, i < source.outputs[index].encoding.size → ∀ patch ∈ loaded.patches,
      ¬ (patch.rva ≤ source.codeBase + ByteLayout.offset source.splice.finalSizes index + i ∧
        source.codeBase + ByteLayout.offset source.splice.finalSizes index + i < patch.rva + 8))
    {kind : Rel32.Kind} {target : Nat} {resolved : SignedRel32.Resolved}
    (detail : source.outputs[index].detail = .branch kind target resolved)
    {choice : CheckedChoice}
    (step : RawStep loaded realization environment interpretation graph before
      (.cpu choice) event after nextGraph) :
    EdgeAgreement graph before event after nextGraph ∧
    ∃ (policy : CpuAccessPolicy) (outcome : CpuOutcome),
      before.control = .caller policy.context ∧
      Cpu.policy? loaded before.machine = some policy ∧
      CheckedExecution.CheckedStep policy before.machine choice outcome ∧
      after = before.withMachine outcome.state ∧ (
    (∃ (flags : RegisterSemantics.Flags Bool)
      (success : BodyComputationFactory.BranchSuccess policy before.machine),
      choice = .normal flags ∧ outcome = .progressed success.result .completed ∧
      FetchFactory.fetch policy before.machine = .ok success.fetched ∧
      success.receipt.execution.fetch.site.encoding = source.outputs[index].encoding ∧
      success.instruction.kind = kind ∧ success.instruction.displacement = resolved.bits ∧
      success.result.gpr = before.machine.gpr ∧
      success.result.rip = if success.instruction.taken before.machine.statusFlags then
        BitVec.ofNat 64 ((SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
          ByteLayout.offset source.splice.finalSizes target)
        else BitVec.ofNat 64 ((SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
          ByteLayout.offset source.splice.finalSizes index + Rel32.encodedSize kind)) ∨
    ∃ reached reason, outcome = .outsideProfile reached reason) := by
  obtain ⟨policy, outcome, control, selected, checked, installed⟩ := step.cpu_checked
  exact ⟨step.agreement, policy, outcome, control, selected, checked, installed,
    SourceBranchExecution.sourceBranch_checked_cases binding loaded contains selected
      present index bounded rip cells outside detail checked⟩

end Grass.Platform.Win32.Raw.RawStep
