import Grass.Assembly.SourceInitialization
import Grass.Assembly.SourcePrologue
import Grass.Assembly.SourceTemplates

/-! Draft checked splice. It constructs instruction templates and coordinates;
it does not resolve branch or external/static symbol byte displacements. -/
namespace Grass.Assembly.SourceSplice

open Grass.ISA.X86

def sourceFinalIndex (savedCount initializerCount sourceIndex : Nat) : Nat :=
  if sourceIndex < savedCount then sourceIndex else sourceIndex + 1 + initializerCount

private def spliceIndex (savedCount insertedCount sourceIndex : Nat) : Nat :=
  if sourceIndex < savedCount then sourceIndex else sourceIndex + insertedCount

inductive FinalTemplate where
  | encoded (encoding : InsnEncoding)
  | branch (kind : Grass.ISA.X86.Rel32.Kind) (translatedTarget : Nat)
  | ripAddress (destination : Gpr) (symbol : String) (prototype : InsnEncoding)
  | ripCall (symbol : String) (prototype : InsnEncoding)
  | sizeOf32 (destination : Gpr) (symbol : String) (prototype : InsnEncoding)
deriving Repr, DecidableEq

def FinalTemplate.size : FinalTemplate → Nat
  | .encoded encoding => encoding.size
  | .branch kind _ => Grass.ISA.X86.Rel32.encodedSize kind
  | .ripAddress _ _ prototype | .ripCall _ prototype | .sizeOf32 _ _ prototype => prototype.size

def translate (savedCount initializerCount : Nat) : SourceTemplates.Template → FinalTemplate
  | .encoded encoding => .encoded encoding
  | .branch kind target => .branch kind (sourceFinalIndex savedCount initializerCount target)
  | .ripAddress destination symbol prototype => .ripAddress destination symbol prototype
  | .ripCall symbol prototype => .ripCall symbol prototype
  | .sizeOf32 destination symbol prototype => .sizeOf32 destination symbol prototype

theorem translate_size (savedCount initializerCount : Nat) (template : SourceTemplates.Template) :
    (translate savedCount initializerCount template).size = template.size := by
  cases template <;> rfl

theorem FinalTemplate.size_pos (template : FinalTemplate) : 0 < template.size := by
  cases template with
  | encoded encoding | ripAddress _ _ encoding | ripCall _ encoding | sizeOf32 _ _ encoding =>
      exact encoding.size_pos
  | branch kind target =>
      change 0 < (Grass.ISA.X86.Rel32.encode kind 0).size
      exact InsnEncoding.size_pos _

inductive FinalOutput (frame : SourceFrame.Result) (rootOffset : Nat) where
  | source (output : SourceTemplates.Output frame rootOffset)
  | allocation (encoding : InsnEncoding)
  | initialization (entry : SourceInitialization.Entry)

def FinalOutput.template {frame rootOffset} (savedCount initializerCount : Nat) :
    FinalOutput frame rootOffset → FinalTemplate
  | .source output => translate savedCount initializerCount output.template
  | .allocation encoding => .encoded encoding
  | .initialization entry => .encoded entry.store.encoding

def FinalOutput.source? {frame rootOffset} : FinalOutput frame rootOffset →
    Option (SourceTemplates.Output frame rootOffset)
  | .source output => some output
  | .allocation _ | .initialization _ => none

def spliceOutputs {frame : SourceFrame.Result} {rootOffset : Nat} : Nat →
    List (FinalOutput frame rootOffset) → List (SourceTemplates.Output frame rootOffset) →
      List (FinalOutput frame rootOffset)
  | 0, inserted, source => inserted ++ source.map .source
  | _ + 1, inserted, [] => inserted
  | saved + 1, inserted, output :: source =>
      .source output :: spliceOutputs saved inserted source

private theorem sourceMapAll {frame rootOffset}
    (xs : List (SourceTemplates.Output frame rootOffset)) :
    (xs.map FinalOutput.source).filterMap FinalOutput.source? = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [FinalOutput.source?, ih]

theorem spliceOutputs_source_order {frame rootOffset} (saved : Nat)
    (inserted : List (FinalOutput frame rootOffset))
    (insertedNone : ∀ output ∈ inserted, FinalOutput.source? output = none)
    (source : List (SourceTemplates.Output frame rootOffset)) :
    (spliceOutputs saved inserted source).filterMap FinalOutput.source? = source := by
  induction saved generalizing source with
  | zero =>
      have erased : inserted.filterMap FinalOutput.source? = [] := by
        rw [List.filterMap_eq_nil_iff]
        exact insertedNone
      rw [show spliceOutputs 0 inserted source = inserted ++ source.map FinalOutput.source by rfl,
        List.filterMap_append, erased, sourceMapAll]
      rfl
  | succ saved ih =>
      cases source with
      | nil =>
          have erased : inserted.filterMap FinalOutput.source? = [] := by
            rw [List.filterMap_eq_nil_iff]
            exact insertedNone
          simp [spliceOutputs, erased]
      | cons output source =>
          simp only [spliceOutputs, List.filterMap_cons, FinalOutput.source?]
          rw [ih source]

theorem spliceOutputs_source_at {frame rootOffset} (saved : Nat)
    (inserted : List (FinalOutput frame rootOffset))
    (source : List (SourceTemplates.Output frame rootOffset))
    (index : Nat) (bounded : index < source.length) :
    (spliceOutputs saved inserted source)[spliceIndex saved inserted.length index]? =
      (source[index]?).map FinalOutput.source := by
  induction saved generalizing source index with
  | zero =>
      simp [spliceOutputs, spliceIndex, List.getElem?_append_right, bounded]
  | succ saved ih =>
      cases source with
      | nil => simp at bounded
      | cons output source =>
          cases index with
          | zero => simp [spliceOutputs, spliceIndex]
          | succ index =>
              simp only [List.length_cons, Nat.succ_lt_succ_iff] at bounded
              have step := ih source index bounded
              by_cases h : index < saved
              · simp [spliceOutputs, spliceIndex, h] at step ⊢
                exact step
              · simp [spliceOutputs, spliceIndex, h] at step ⊢
                rw [show index + 1 + inserted.length = (index + inserted.length) + 1 by omega]
                simp only [List.getElem?_cons_succ]
                exact step

theorem spliceOutputs_inserted_at {frame rootOffset} (saved : Nat)
    (inserted : List (FinalOutput frame rootOffset))
    (source : List (SourceTemplates.Output frame rootOffset))
    (savedBound : saved ≤ source.length) (index : Nat) (bounded : index < inserted.length) :
    (spliceOutputs saved inserted source)[saved + index]? = inserted[index]? := by
  induction saved generalizing source with
  | zero => simp [spliceOutputs, List.getElem?_append_left, bounded]
  | succ saved ih =>
      cases source with
      | nil => simp at savedBound
      | cons output source =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at savedBound
          have step := ih source savedBound
          rw [show Nat.succ saved + index = Nat.succ (saved + index) by omega]
          simpa [spliceOutputs] using step

theorem spliceOutputs_length {frame rootOffset} (saved : Nat)
    (inserted : List (FinalOutput frame rootOffset))
    (source : List (SourceTemplates.Output frame rootOffset))
    (savedBound : saved ≤ source.length) :
    (spliceOutputs saved inserted source).length = source.length + inserted.length := by
  induction saved generalizing source with
  | zero => simp [spliceOutputs, Nat.add_comm]
  | succ saved ih =>
      cases source with
      | nil => simp at savedBound
      | cons output source =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at savedBound
          simp [spliceOutputs, ih source savedBound]
          omega

def finalOutputs {frame : SourceFrame.Result} {rootOffset : Nat}
    (source : SourceTemplates.Result frame rootOffset)
    (prologue : SourcePrologue.Result) (initialization : SourceInitialization.Result) :
    List (FinalOutput frame rootOffset) :=
  let savedCount := frame.saved.savedItems.length
  spliceOutputs savedCount
    (.allocation prologue.allocation.encoding ::
      initialization.entries.map .initialization) source.outputs

def sourceEncoding? {frame rootOffset} (output : SourceTemplates.Output frame rootOffset) :
    Option InsnEncoding :=
  match output.template with | .encoded encoding => some encoding | _ => none

structure Result (frame : SourceFrame.Result) (rootOffset : Nat) where
  private mk ::
  source : SourceTemplates.Result frame rootOffset
  prologue : SourcePrologue.Result
  initialization : SourceInitialization.Result
  outputs : List (FinalOutput frame rootOffset)
  prologueFrame : prologue.frame = frame
  initializationFrame : initialization.frame = frame
  initializationRoot : initialization.rootOffset = rootOffset
  prefixEncodingsExact :
    (source.outputs.take frame.saved.savedItems.length).mapM sourceEncoding? =
      some (prologue.generated.take frame.saved.savedItems.length)
  allocationAtBoundary :
    prologue.generated[frame.saved.savedItems.length]? = some prologue.allocation.encoding
  outputsExact : outputs = finalOutputs source prologue initialization
  bodyStartExact :
    Grass.Assembly.ByteLayout.offset
      (outputs.map (fun output =>
        (output.template frame.saved.savedItems.length initialization.entries.length).size))
      (sourceFinalIndex frame.saved.savedItems.length initialization.entries.length
        frame.saved.savedItems.length) =
    (Grass.Assembly.ByteLayout.sizes prologue.generated).sum +
      (initialization.entries.map fun entry => entry.store.encoding.size).sum

def derive? (frame : SourceFrame.Result) (rootOffset : Nat) : Option (Result frame rootOffset) := do
  let source ← SourceTemplates.derive? frame rootOffset
  match hpResult : SourcePrologue.generate? frame with
  | none => none
  | some prologue =>
    match hiResult : SourceInitialization.resolve? frame rootOffset with
    | none => none
    | some initialization =>
      if he : (source.outputs.take frame.saved.savedItems.length).mapM sourceEncoding? =
          some (prologue.generated.take frame.saved.savedItems.length) then
        if ha : prologue.generated[frame.saved.savedItems.length]? =
            some prologue.allocation.encoding then
          let outputs := finalOutputs source prologue initialization
          if hb : Grass.Assembly.ByteLayout.offset
              (outputs.map (fun output =>
                (output.template frame.saved.savedItems.length initialization.entries.length).size))
              (sourceFinalIndex frame.saved.savedItems.length initialization.entries.length
                frame.saved.savedItems.length) =
              (Grass.Assembly.ByteLayout.sizes prologue.generated).sum +
                (initialization.entries.map fun entry => entry.store.encoding.size).sum then
            have hp := SourcePrologue.generate?_frame hpResult
            have hi := SourceInitialization.resolve?_source hiResult
            some ⟨source, prologue, initialization, outputs, hp, hi.1, hi.2,
              he, ha, rfl, hb⟩
          else none
        else none
      else none

def Result.finalTemplates {frame rootOffset} (result : Result frame rootOffset) :
    List FinalTemplate :=
  result.outputs.map fun output =>
    output.template frame.saved.savedItems.length result.initialization.entries.length

def Result.finalSizes {frame rootOffset} (result : Result frame rootOffset) : List Nat :=
  result.finalTemplates.map FinalTemplate.size

def Result.entryOffset {_frame _rootOffset} (_result : Result _frame _rootOffset) : Nat := 0

def Result.unwindEndOffset {frame rootOffset} (result : Result frame rootOffset) : Nat :=
  (Grass.Assembly.ByteLayout.sizes result.prologue.generated).sum

def Result.initializerStartOffset {frame rootOffset} (result : Result frame rootOffset) : Nat :=
  result.unwindEndOffset

def Result.bodyStartOffset {frame rootOffset} (result : Result frame rootOffset) : Nat :=
  result.unwindEndOffset +
    (result.initialization.entries.map fun entry => entry.store.encoding.size).sum

def Result.sourcePosition {frame rootOffset} (result : Result frame rootOffset)
    (sourceIndex : Nat) : Nat :=
  Grass.Assembly.ByteLayout.offset result.finalSizes
    (sourceFinalIndex frame.saved.savedItems.length result.initialization.entries.length sourceIndex)

theorem Result.entry_offset {frame rootOffset} (result : Result frame rootOffset) :
    result.entryOffset = 0 := rfl

theorem Result.initializers_follow_unwind {frame rootOffset} (result : Result frame rootOffset) :
    result.initializerStartOffset = result.unwindEndOffset := rfl

theorem Result.boundary_is_body_start {frame rootOffset} (result : Result frame rootOffset) :
    result.sourcePosition frame.saved.savedItems.length = result.bodyStartOffset := by
  simpa [Result.sourcePosition, Result.finalSizes, Result.finalTemplates,
    Result.bodyStartOffset, Result.unwindEndOffset, Function.comp_def] using result.bodyStartExact

theorem Result.source_order {frame rootOffset} (result : Result frame rootOffset) :
    result.outputs.filterMap FinalOutput.source? = result.source.outputs := by
  rw [result.outputsExact]
  apply spliceOutputs_source_order
  intro output member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · rfl
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    rfl

theorem Result.source_instruction_count {frame rootOffset} (result : Result frame rootOffset) :
    (result.outputs.filterMap FinalOutput.source?).length =
      frame.program.collected.code.length := by
  rw [result.source_order, result.source.output_count]

theorem Result.final_instruction_count {frame rootOffset} (result : Result frame rootOffset) :
  result.outputs.length = frame.program.collected.code.length + 1 +
      result.initialization.entries.length := by
  rw [result.outputsExact]
  have prefixBound : frame.saved.savedItems.length ≤ result.source.outputs.length := by
    rw [result.source.output_count]
    have partition := frame.saved.code_partition
    rw [frame.saved_program] at partition
    rw [partition]
    simp
  change (spliceOutputs frame.saved.savedItems.length
    (FinalOutput.allocation result.prologue.allocation.encoding ::
      result.initialization.entries.map FinalOutput.initialization)
    result.source.outputs).length = _
  rw [spliceOutputs_length _ _ _ prefixBound]
  simp [result.source.output_count]
  omega

theorem Result.saved_count_le_source {frame rootOffset} (result : Result frame rootOffset) :
    frame.saved.savedItems.length ≤ result.source.outputs.length := by
  rw [result.source.output_count]
  have partition := frame.saved.code_partition
  rw [frame.saved_program] at partition
  rw [partition]
  simp

theorem Result.source_output_at_final_index {frame rootOffset}
    (result : Result frame rootOffset) (sourceIndex : Nat)
    (sourceBound : sourceIndex < result.source.outputs.length) :
    result.outputs[sourceFinalIndex frame.saved.savedItems.length
      result.initialization.entries.length sourceIndex]? =
      (result.source.outputs[sourceIndex]?).map FinalOutput.source := by
  rw [result.outputsExact]
  change (spliceOutputs frame.saved.savedItems.length
    (FinalOutput.allocation result.prologue.allocation.encoding ::
      result.initialization.entries.map FinalOutput.initialization)
    result.source.outputs)[_]? = _
  let inserted : List (FinalOutput frame rootOffset) :=
    FinalOutput.allocation result.prologue.allocation.encoding ::
      result.initialization.entries.map FinalOutput.initialization
  have lookup := spliceOutputs_source_at
    frame.saved.savedItems.length inserted
    result.source.outputs sourceIndex sourceBound
  have indexEq : sourceFinalIndex frame.saved.savedItems.length
      result.initialization.entries.length sourceIndex =
      spliceIndex frame.saved.savedItems.length
        inserted.length sourceIndex := by
    simp [inserted, spliceIndex, sourceFinalIndex]
    split <;> omega
  change (spliceOutputs frame.saved.savedItems.length inserted result.source.outputs)[_]? = _
  rw [indexEq]
  exact lookup

theorem Result.branch_template_at_final_index {frame rootOffset}
    (result : Result frame rootOffset) (sourceIndex : Nat)
    (sourceBound : sourceIndex < result.source.outputs.length)
    (output : SourceTemplates.Output frame rootOffset)
    (sourceAt : result.source.outputs[sourceIndex]? = some output)
    (kind : Grass.ISA.X86.Rel32.Kind) (targetIndex : Nat)
    (branch : output.template = .branch kind targetIndex) :
    (result.outputs[sourceFinalIndex frame.saved.savedItems.length
      result.initialization.entries.length sourceIndex]?).map
        (FinalOutput.template frame.saved.savedItems.length
          result.initialization.entries.length) =
      some (.branch kind (sourceFinalIndex frame.saved.savedItems.length
        result.initialization.entries.length targetIndex)) := by
  rw [result.source_output_at_final_index sourceIndex sourceBound, sourceAt]
  simp [FinalOutput.template, translate, branch]

theorem Result.allocation_at_boundary {frame rootOffset} (result : Result frame rootOffset) :
    result.outputs[frame.saved.savedItems.length]? =
      some (.allocation result.prologue.allocation.encoding) := by
  rw [result.outputsExact]
  have savedBound := result.saved_count_le_source
  simpa [finalOutputs] using spliceOutputs_inserted_at
    frame.saved.savedItems.length
    (FinalOutput.allocation result.prologue.allocation.encoding ::
      result.initialization.entries.map FinalOutput.initialization)
    result.source.outputs savedBound 0 (by simp)

theorem Result.initializer_at {frame rootOffset} (result : Result frame rootOffset)
    (index : Nat) (bounded : index < result.initialization.entries.length) :
    result.outputs[frame.saved.savedItems.length + 1 + index]? =
      (result.initialization.entries[index]?).map FinalOutput.initialization := by
  rw [result.outputsExact]
  have savedBound := result.saved_count_le_source
  have lookup := spliceOutputs_inserted_at
    frame.saved.savedItems.length
    (FinalOutput.allocation result.prologue.allocation.encoding ::
      result.initialization.entries.map FinalOutput.initialization)
    result.source.outputs savedBound (index + 1) (by simp [bounded])
  change (spliceOutputs frame.saved.savedItems.length
    (FinalOutput.allocation result.prologue.allocation.encoding ::
      result.initialization.entries.map FinalOutput.initialization)
    result.source.outputs)[frame.saved.savedItems.length + 1 + index]? = _
  rw [show frame.saved.savedItems.length + 1 + index =
    frame.saved.savedItems.length + (index + 1) by omega, lookup]
  simp [bounded]

theorem Result.every_final_size_positive {frame rootOffset} (result : Result frame rootOffset)
    (size : Nat) (member : size ∈ result.finalSizes) : 0 < size := by
  simp only [Result.finalSizes, List.mem_map] at member
  obtain ⟨template, _, rfl⟩ := member
  exact template.size_pos

theorem Result.source_final_index_in_bounds {frame rootOffset} (result : Result frame rootOffset)
    (sourceIndex : Nat) (sourceBound : sourceIndex < frame.program.collected.code.length) :
    sourceFinalIndex frame.saved.savedItems.length result.initialization.entries.length sourceIndex <
      result.outputs.length := by
  rw [result.final_instruction_count]
  by_cases isPrefix : sourceIndex < frame.saved.savedItems.length
  · simp [sourceFinalIndex, isPrefix]
    omega
  · simp [sourceFinalIndex, isPrefix]
    omega

theorem Result.source_position_in_final_bytes {frame rootOffset}
    (result : Result frame rootOffset) (sourceIndex : Nat)
    (sourceBound : sourceIndex < frame.program.collected.code.length) :
    result.sourcePosition sourceIndex < result.finalSizes.sum := by
  have indexBound :
      sourceFinalIndex frame.saved.savedItems.length result.initialization.entries.length sourceIndex <
        result.finalSizes.length := by
    rw [show result.finalSizes.length = result.outputs.length by
      simp [Result.finalSizes, Result.finalTemplates]]
    exact result.source_final_index_in_bounds sourceIndex sourceBound
  exact Grass.Assembly.ByteLayout.offset_lt_total result.finalSizes _ indexBound
    (result.every_final_size_positive _ (List.getElem_mem indexBound))

theorem sourceFinalIndex_body {savedCount initializerCount sourceIndex : Nat}
    (body : savedCount ≤ sourceIndex) :
    sourceFinalIndex savedCount initializerCount sourceIndex =
      sourceIndex + 1 + initializerCount := by
  simp [sourceFinalIndex, Nat.not_lt.mpr body]

theorem Result.branch_target_after_insertions {frame rootOffset}
    (result : Result frame rootOffset) (flow : X86ControlFlow.Flow)
    (flowMember : flow ∈ frame.program.flows) (targetIndex : Nat)
    (taken : targetIndex ∈ SavedPrefix.localTakenTargets flow) :
    sourceFinalIndex frame.saved.savedItems.length result.initialization.entries.length targetIndex =
      targetIndex + 1 + result.initialization.entries.length := by
  apply sourceFinalIndex_body
  apply frame.saved.noReentryInsidePrefix flow
  · rwa [frame.saved_program]
  · exact taken

end Grass.Assembly.SourceSplice
