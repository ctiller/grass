import Grass.Assembly.SourceBytes
import Grass.Assembly.SourceUnwind

/-! Proofs connecting the source-derived prologue to the
resolved encoding and byte prefixes. This states encoding/layout facts only. -/

namespace Grass.Assembly.SourceResolve

open Grass.ISA.X86

private theorem mapM_getElem? {α β : Type} (f : α → Option β)
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) (i : Nat) :
    ys[i]? = xs[i]?.bind f := by
  induction xs generalizing ys i with
  | nil => simp at h; subst ys; simp
  | cons x xs ih =>
      simp only [List.mapM_cons] at h
      cases hx : f x with
      | none => simp [hx] at h
      | some y =>
          rw [hx] at h
          cases ht : List.mapM f xs with
          | none => simp [ht] at h
          | some tail =>
            simp [ht] at h
            subst ys
            cases i with
            | zero => simp [hx]
            | succ i => simpa using ih ht i

/-- Resolution of an already encoded template retains that exact encoding. -/
theorem Output.encoding_of_template_encoded {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} {symbols : Symbols} {codeBase : Nat}
    (output : Output splice symbols codeBase) (expected : InsnEncoding)
    (encoded : output.template = .encoded expected) : output.encoding = expected := by
  cases detailEq : output.detail with
  | encoded =>
      have valid := output.detailExact
      rw [detailEq] at valid
      rw [encoded] at valid
      injection valid with equality
      exact equality.symm
  | branch kind target resolved =>
      have valid := output.detailExact
      rw [detailEq] at valid
      rw [encoded] at valid
      cases valid.1
  | ripStatic destination name symbol resolved =>
      have valid := output.detailExact
      rw [detailEq] at valid
      obtain ⟨prototype, impossible⟩ := valid.1
      rw [encoded] at impossible
      cases impossible
  | ripImport name symbol resolved =>
      have valid := output.detailExact
      rw [detailEq] at valid
      obtain ⟨prototype, impossible⟩ := valid.1
      rw [encoded] at impossible
      cases impossible
  | sizeOf32 destination name symbol =>
      have valid := output.detailExact
      rw [detailEq] at valid
      obtain ⟨prototype, impossible⟩ := valid.2.1
      rw [encoded] at impossible
      cases impossible

private theorem output_at {frame rootOffset} (result : Result frame rootOffset)
    (index : Nat) (bound : index < result.outputs.length) :
    result.splice.outputs[index]? = some result.outputs[index].origin := by
  have exact := result.outputs[index].originAt
  rw [result.output_index_at index bound] at exact
  exact exact

/-- Every saved-register position in the resolved stream is exactly the
corresponding generated prologue encoding. -/
theorem Result.saved_encoding_at {frame rootOffset} (result : Result frame rootOffset)
    (index : Nat) (saved : index < frame.saved.savedItems.length) :
    result.encodings[index]? = result.splice.prologue.generated[index]? := by
  have sourceBound : index < result.splice.source.outputs.length :=
    Nat.lt_of_lt_of_le saved result.splice.saved_count_le_source
  let sourceOutput := result.splice.source.outputs[index]
  have sourceAt : result.splice.source.outputs[index]? = some sourceOutput :=
    List.getElem?_eq_getElem sourceBound
  have finalAt := result.splice.source_output_at_final_index index sourceBound
  simp [SourceSplice.sourceFinalIndex, saved, sourceAt] at finalAt
  have outputBound : index < result.outputs.length := by
    have programBound : index < frame.program.collected.code.length := by
      rw [← result.splice.source.output_count]
      exact sourceBound
    have spliceBound := result.splice.source_final_index_in_bounds index programBound
    rw [result.countExact]
    simpa [SourceSplice.sourceFinalIndex, saved] using spliceBound
  have originAt := output_at result index outputBound
  rw [finalAt] at originAt
  have originEq : result.outputs[index].origin = .source sourceOutput := by
    simpa using Option.some.inj originAt.symm
  have mapped := mapM_getElem? SourceSplice.sourceEncoding?
    result.splice.prefixEncodingsExact index
  simp only [List.getElem?_take, if_pos saved] at mapped
  change result.splice.prologue.generated[index]? =
    result.splice.source.outputs[index]?.bind SourceSplice.sourceEncoding? at mapped
  rw [sourceAt] at mapped
  have allocationBound : frame.saved.savedItems.length <
      result.splice.prologue.generated.length :=
    (List.getElem?_eq_some_iff.mp result.splice.allocationAtBoundary).choose
  have generatedBound : index < result.splice.prologue.generated.length := by omega
  rw [List.getElem?_eq_getElem generatedBound] at mapped
  have sourceTemplate : sourceOutput.template =
      .encoded (result.splice.prologue.generated[index]) := by
    cases templateEq : sourceOutput.template with
    | encoded encoding =>
        simp [SourceSplice.sourceEncoding?, templateEq] at mapped
        simp [mapped]
    | branch kind target => simp [SourceSplice.sourceEncoding?, templateEq] at mapped
    | ripAddress destination symbol prototype =>
        simp [SourceSplice.sourceEncoding?, templateEq] at mapped
    | ripCall symbol prototype => simp [SourceSplice.sourceEncoding?, templateEq] at mapped
    | sizeOf32 destination symbol prototype =>
        simp [SourceSplice.sourceEncoding?, templateEq] at mapped
  have template : result.outputs[index].template =
      .encoded (result.splice.prologue.generated[index]) := by
    rw [result.outputs[index].templateExact, originEq]
    simp [SourceSplice.FinalOutput.template, sourceTemplate, SourceSplice.translate]
  have exact := result.outputs[index].encoding_of_template_encoded _ template
  simp only [Result.encodings, List.getElem?_map]
  rw [List.getElem?_eq_getElem outputBound]
  rw [List.getElem?_eq_getElem generatedBound]
  simpa using congrArg some exact

/-- The inserted allocation position retains the generated allocation encoding. -/
theorem Result.allocation_encoding_at {frame rootOffset} (result : Result frame rootOffset) :
    result.encodings[frame.saved.savedItems.length]? =
      some result.splice.prologue.allocation.encoding := by
  let index := frame.saved.savedItems.length
  have spliceAt := result.splice.allocation_at_boundary
  have outputBound : index < result.outputs.length := by
    have savedLe : frame.saved.savedItems.length ≤ frame.program.collected.code.length := by
      rw [← result.splice.source.output_count]
      exact result.splice.saved_count_le_source
    rw [result.countExact, result.splice.final_instruction_count]
    omega
  have originAt := output_at result index outputBound
  rw [spliceAt] at originAt
  have originEq : result.outputs[index].origin =
      .allocation result.splice.prologue.allocation.encoding := by
    simpa using Option.some.inj originAt.symm
  have template : result.outputs[index].template =
      .encoded result.splice.prologue.allocation.encoding := by
    rw [result.outputs[index].templateExact, originEq]
    rfl
  have exact := result.outputs[index].encoding_of_template_encoded _ template
  simp only [Result.encodings, List.getElem?_map]
  rw [List.getElem?_eq_getElem outputBound]
  simpa using congrArg some exact

/-- The complete saved-push plus allocation sequence is the exact encoding prefix. -/
theorem Result.prologue_encoding_prefix {frame rootOffset} (result : Result frame rootOffset) :
    result.encodings.take result.splice.prologue.generated.length =
      result.splice.prologue.generated := by
  apply List.ext_getElem?
  intro index
  by_cases inGenerated : index < result.splice.prologue.generated.length
  · have shape := result.splice.prologue.generated_shape
    have lengthEq : result.splice.prologue.generated.length =
        frame.saved.savedItems.length + 1 := by
      rw [shape]
      rw [result.splice.prologueFrame]
      simp [frame.saved.prefix_length]
    rw [List.getElem?_take, if_pos (by omega)]
    by_cases saved : index < frame.saved.savedItems.length
    · exact result.saved_encoding_at index saved
    · have indexEq : index = frame.saved.savedItems.length := by omega
      subst index
      rw [result.splice.allocationAtBoundary]
      exact result.allocation_encoding_at
  · rw [List.getElem?_take, if_neg inGenerated]
    exact (List.getElem?_eq_none (Nat.le_of_not_gt inGenerated)).symm

/-- Serializing the resolved stream yields exactly the source-derived prologue
bytes followed by serialization of the remaining resolved encodings. -/
theorem Result.prologue_bytes_append {frame rootOffset} (result : Result frame rootOffset) :
    result.bytes.toList =
      ByteLayout.emitted result.splice.prologue.generated ++
        ByteLayout.emitted (result.encodings.drop result.splice.prologue.generated.length) := by
  change ByteLayout.emitted result.encodings = _
  have split := congrArg ByteLayout.emitted
    (List.take_append_drop result.splice.prologue.generated.length result.encodings)
  rw [ByteLayout.emitted_append, result.prologue_encoding_prefix] at split
  exact split.symm

/-- The prefix byte count is exactly the count stored in the checked unwind layout. -/
theorem Result.prologue_byte_count {frame rootOffset} (result : Result frame rootOffset) :
    (ByteLayout.emitted result.splice.prologue.generated).length =
      result.splice.prologue.unwindLayout.sizeOfProlog.toNat :=
  result.splice.prologue.stored_prologue_size.symm

/-- The checked metadata header selects the exact generated prologue prefix
from the final code bytes. This does not establish semantic unwind reversal. -/
theorem Result.unwind_header_prefix {frame rootOffset} (result : Result frame rootOffset)
    (metadata : SourceUnwind.Result result.splice.prologue) :
    result.bytes.toList.take metadata.info.layout.sizeOfProlog.toNat =
      ByteLayout.emitted result.splice.prologue.generated := by
  rw [metadata.prologue_size, result.prologue_bytes_append]
  simp

end Grass.Assembly.SourceResolve
