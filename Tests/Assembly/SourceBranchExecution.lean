import Grass.Assembly.SourceBranchExecution
import Grass.Platform.Win32.RawSourceBranch
import Grass.Assembly.SourceLinkedImage
import Tests.Assembly.SourceLiteral

/-! One source-derived branch site with arbitrary labels. The incoming state is
placed at that site; this fixture does not claim execution of a whole program. -/

namespace Grass.Tests.Assembly.SourceBranchExecution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Artifact Grass.Artifact.PE
open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

private def text := source_chars "def branchingSample : MachineSource targetPlan := withCallFrame ExitProcess asm_source (statics := objects) {\nagain:\n je finished\n ja finished\n jmp again\nfinished:\n ud2\nunusedImport:\n call qword ptr [rip+__imp_ExitProcess]\n ud2\n}"
private def body := (SourceInput.extractSourceChars text).toOption.get (by decide +kernel)
private def frame := (SourceFrame.derive? body).get (by decide +kernel)
private def splice := (SourceSplice.derive? frame 0).get (by decide +kernel)
private def table := StaticObjects.checked [⟨"unused", 1, .rodata, .fromList [0]⟩]
  (by decide)
private def statics := (StaticSection.layout? table ⟨Text.utf8 ".data", by decide⟩ 0x40000040).get (by decide)
private def requests := (SourceImportRequests.resolve? splice "kernel32.dll").get (by decide +kernel)
private def sections : SourceLinkedImage.Sections :=
  ⟨⟨Text.utf8 ".text", by decide⟩, 0x60000020,
    ⟨Text.utf8 ".pdata", by decide⟩, ⟨Text.utf8 ".xdata", by decide⟩⟩
private def linked := (SourceLinkedImage.build? splice statics sections requests).get (by decide +kernel)
private def image : ImageInput := ⟨linked.plan, (writeImage linked.plan).toHostBytes, rfl⟩

private def allocations : FreshSupply AllocTag := .initial
private def storages : FreshSupply StorageTag := .initial
private def epoch : EpochId := (FreshSupply.initial : FreshSupply EpochTag).fresh.1
private def caller : ContextId := (FreshSupply.initial : FreshSupply ContextTag).fresh.1
private def provider : ContextId := (FreshSupply.initial : FreshSupply ContextTag).fresh.2.fresh.1
private def stack : AllocId := allocations.fresh.1
private def storage : StorageId := storages.fresh.1
private def returnAddress : BitVec 64 := 0x70000000
private def stackRecord : AllocationRecord :=
  { extent := ⟨0, 256⟩, epoch, space := .cpuVirtual, source := .stack,
    owners := [caller], permission := .readWrite, live := true, backing := storage,
    origin := 0, base := some 0x100000 }
private def memory : MemoryState :=
  let installed := (MemoryState.empty.installBacking? storage
    ⟨256, ByteStore.empty.write 136 (Binary.writeLittleEndian (count := 8) returnAddress).toList true⟩).get (by decide)
  (installed.allocate? stack stackRecord).get (by decide)
private def identities : Nat → FreshSupply AllocTag → FreshSupply StorageTag → List RegionIdentity
  | 0, _, _ => []
  | n + 1, a, s => ⟨a.fresh.1, s.fresh.1, epoch⟩ :: identities n a.fresh.2 s.fresh.2
private def inputs : EntryInputs :=
  { environment := { MachineState.initial memory with
      contexts := FiniteMap.empty.insert caller .thread |>.insert provider .externalAgent },
    thread := caller, independentContext := provider,
    identities := identities (linked.plan.layout.placed.length + 1) allocations.fresh.2 storages.fresh.2,
    targets := .fromList [.fromList [0x7fff0000]],
    stack := ⟨stack, 136, 64, returnAddress⟩,
    gpr := fun register => if register = .rsp then 0x100088 else 0,
    rflags := 0x202 }
private def loaded := (initialize? image inputs).get (by decide +kernel)
private def index := linked.source.outputs.findIdx fun output =>
  match output.detail with | .branch .equal _ _ => true | _ => false
private theorem bounded : index < linked.source.outputs.length := by decide +kernel
private def region := SourceLoadedImage.codeRegion linked.code loaded
private def before (zero : Bool) : State :=
  { loaded.initialState with
    rip := addressOf region.region.base (ByteLayout.offset linked.source.splice.finalSizes index),
    rflags := if zero then 0x242 else 0x202 }

set_option maxHeartbeats 400000
private def branch := (match linked.source.outputs[index].detail with
  | .branch .equal target resolved => some (target, resolved)
  | _ => none).get (by decide +kernel)
private theorem detail : linked.source.outputs[index].detail =
    .branch .equal branch.1 branch.2 := by rfl
private theorem firstByte : linked.source.bytes.get?
    (ByteLayout.offset linked.source.splice.finalSizes index) = some 0x0f := by decide +kernel
private theorem contains (zero : Bool) : ContainsCodeAddress region.region (before zero).rip :=
  LoadedCodeRoot.codeRegion_contains (source := linked.source) (image := image) (inputs := inputs) (sectionIndex := 0) linked.code loaded (by decide +kernel) firstByte
private def policy (zero : Bool) :=
  (Cpu.policy? loaded (before zero)).get
    (SourceFetchPolicy.policy_available (source := linked.source) (image := image) (inputs := inputs) (sectionIndex := 0) linked.code loaded (before zero) (contains zero))
private theorem selected (zero : Bool) : Cpu.policy? loaded (before zero) = some (policy zero) :=
  (Option.some_get _).symm
private theorem present (zero : Bool) :
    (before zero).machine.memory.allocations.lookup region.region.allocId =
      some region.region.allocationRecord :=
  (loaded.imagePresent region.region region.member).1
private theorem rip (zero : Bool) : (before zero).rip.toNat = region.region.base.toNat +
    ByteLayout.offset linked.source.splice.finalSizes index :=
  LoadedCodeRoot.codeRegion_address (source := linked.source) (image := image) (inputs := inputs) (sectionIndex := 0) linked.code loaded firstByte
private theorem cells (zero : Bool) (offset : Nat) :
    (before zero).machine.memory.cellAt? region.region.allocId offset =
      loaded.initialState.machine.memory.cellAt? region.region.allocId offset := rfl
private theorem outside (i : Nat) (bound : i < linked.source.outputs[index].encoding.size)
    (patch : ImportPatch) (member : patch ∈ loaded.patches) :
    ¬ (patch.rva ≤ linked.source.codeBase + ByteLayout.offset linked.source.splice.finalSizes index + i ∧
      linked.source.codeBase + ByteLayout.offset linked.source.splice.finalSizes index + i < patch.rva + 8) := by
  have width : linked.source.outputs[index].encoding.size = 6 := by rfl
  have beyond : ∀ patch ∈ loaded.patches,
      linked.source.codeBase + ByteLayout.offset linked.source.splice.finalSizes index + 6 ≤ patch.rva := by
    decide +kernel
  have separated := beyond patch member
  omega

-- Keep theorem application from repeatedly unfolding the full checked image.
-- This changes elaborator transparency, not kernel definitions or runtime code.
attribute [irreducible] body frame splice linked loaded
-- This consumer quantifies over every admitted choice, not just successful fetches.
private theorem checked_cases (zero : Bool) {choice : CheckedChoice} {outcome : CpuOutcome}
    (step : CheckedExecution.CheckedStep (policy zero) (before zero) choice outcome) :
    (outcome.state.rip = (if zero then
      BitVec.ofNat 64 (region.region.base.toNat + ByteLayout.offset linked.source.splice.finalSizes branch.1)
      else BitVec.ofNat 64 (region.region.base.toNat + ByteLayout.offset linked.source.splice.finalSizes index + 6))) ∨
    (∃ reached reason, outcome = .outsideProfile reached reason) := by
  rcases Grass.Assembly.SourceBranchExecution.sourceBranch_checked_cases (before := before zero) (policy := policy zero) (choice := choice) (outcome := outcome) (kind := .equal) (target := branch.1) (resolved := branch.2) (source := linked.source) (image := image) (inputs := inputs) (sectionIndex := 0) linked.code loaded
    (contains zero) (selected zero) (present zero) index bounded (rip zero) (cells zero) outside detail step with
    ⟨flags, success, _, completed, _, _, kind, _, _, successor⟩ | failed
  · left
    rw [completed]
    change success.result.rip = _
    rw [successor]
    have taken : success.instruction.taken (before zero).statusFlags = zero := by
      cases instructionEq : success.instruction with
      | jump bits => simp [instructionEq, BranchInstruction.kind] at kind
      | above bits => simp [instructionEq, BranchInstruction.kind] at kind
      | equal bits => cases zero <;> rfl
    rw [taken]
    rfl
  · exact Or.inr failed

-- The same source fixture consumes an actual raw edge, including arbitrary
-- retained protocol metadata and the original event and graphs.
private def rawAt (zero : Bool) (metadata : CallProtocol.Metadata ApiRequest) : ExecutionState.RawState :=
  ⟨before zero, metadata, .caller caller, .empty⟩

example (zero : Bool) (metadata : CallProtocol.Metadata ApiRequest)
    {realization : WriteFile.Realization} {environment : ConsoleEnvironment}
    {interpretation : WriteFile.ReturnInterpretation}
    {graph nextGraph : Raw.Graph} {event : Raw.Event} {after : ExecutionState.RawState}
    {choice : CheckedChoice}
    (step : Raw.RawStep loaded realization environment interpretation graph (rawAt zero metadata)
      (.cpu choice) event after nextGraph) :
    Raw.EdgeAgreement graph (rawAt zero metadata) event after nextGraph ∧
    ∃ outcome : CpuOutcome, after = (rawAt zero metadata).withMachine outcome.state ∧
      CheckedExecution.CheckedStep (policy zero) (before zero) choice outcome ∧
      ((outcome.state.rip = (if zero then
        BitVec.ofNat 64 (region.region.base.toNat + ByteLayout.offset linked.source.splice.finalSizes branch.1)
        else BitVec.ofNat 64 (region.region.base.toNat + ByteLayout.offset linked.source.splice.finalSizes index + 6))) ∨
      (∃ reached reason, outcome = .outsideProfile reached reason)) := by
  obtain ⟨agreement, actualPolicy, outcome, _, actualSelected, checked, installed, _⟩ :=
    Raw.RawStep.cpu_branch_successor
      (source := linked.source) (image := image) (inputs := inputs) (sectionIndex := 0)
      (before := rawAt zero metadata) (after := after) (choice := choice)
      (kind := .equal) (target := branch.1) (resolved := branch.2)
      linked.code loaded (contains zero) (present zero) index bounded (rip zero) (cells zero) outside detail step
  have same : actualPolicy = policy zero := Option.some.inj (actualSelected.symm.trans (selected zero))
  subst actualPolicy
  exact ⟨agreement, outcome, installed, checked, checked_cases zero checked⟩

-- Runtime checks use every branch output from this checked source, rather than
-- copied instruction bytes. Opposite supplied flags test incoming-RFLAGS use.
#eval (do
  for zero in ([false, true] : List Bool) do
    for position in List.range linked.source.outputs.length do
      let some output := linked.source.outputs[position]?
        | throw (IO.userError "source branch index missing")
      match output.detail with
      | .branch kind target _ =>
        let state := { before zero with
          rip := addressOf region.region.base (ByteLayout.offset linked.source.splice.finalSizes position) }
        let some actualPolicy := Cpu.policy? loaded state
          | throw (IO.userError "source branch policy unavailable")
        let taken := match kind with
          | .jump => true
          | .equal => zero
          | .above => !zero
        let expected := if taken == true then
          BitVec.ofNat 64 (region.region.base.toNat + ByteLayout.offset linked.source.splice.finalSizes target)
          else BitVec.ofNat 64 (region.region.base.toNat + ByteLayout.offset linked.source.splice.finalSizes position + Rel32.encodedSize kind)
        match CheckedExecution.evaluate actualPolicy state (.normal (before (!zero)).statusFlags) with
        | some (.progressed result .completed) =>
          unless result.rip == expected do throw (IO.userError "source branch successor mismatch")
        | _ => throw (IO.userError "source branch did not complete")
      | _ => pure ()
  -- A conflicting registered context kind refuses the access while preserving
  -- the code allocation and every source byte.
  let refused := { before true with machine := { (before true).machine with
    contexts := (before true).machine.contexts.insert caller .externalAgent } }
  match FetchFactory.fetch (policy true) refused with
  | .error (.access _ _ _) => pure ()
  | _ => throw (IO.userError "expected an actual fetch access refusal")
  match CheckedExecution.evaluate (policy true) refused (.normal refused.statusFlags) with
  | some (.outsideProfile _ _) => pure ()
  | _ => throw (IO.userError "fetch refusal was erased")
  : IO Unit)

example (zero : Bool) (class_ : FaultClassId) :
    CheckedExecution.CheckedStep (policy zero) (before zero) (.fault class_)
      (.outsideProfile (before zero) (.faultTransfer class_)) := rfl
example (zero : Bool) (class_ : FaultClassId) :
    CheckedExecution.CheckedStep (policy zero) (before zero) (.trap class_)
      (.outsideProfile (before zero) (.trapTransfer class_)) := rfl
example (zero : Bool) (vector : BitVec 8) :
    CheckedExecution.CheckedStep (policy zero) (before zero) (.interruption vector)
      (.outsideProfile (before zero) (.interruptionTransfer vector)) := rfl
example (zero : Bool) (class_ : FaultClassId) :
    CheckedExecution.CheckedStep (policy zero) (before zero) (.abort class_)
      (.outsideProfile (before zero) (.abortTransfer class_)) := rfl

end Grass.Tests.Assembly.SourceBranchExecution
