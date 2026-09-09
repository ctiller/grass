import Grass.Assembly.SourceSplice

/-! Target-only proof bridge. Decoder claims are tied to concrete construction
origins, never to an arbitrary `FinalTemplate.encoded`. -/
namespace Grass.Assembly.SourceSpliceDecode

open Grass.ISA.X86

theorem spliceOutputs_member {frame rootOffset} (saved : Nat)
    (inserted : List (SourceSplice.FinalOutput frame rootOffset))
    (source : List (SourceTemplates.Output frame rootOffset))
    (output : SourceSplice.FinalOutput frame rootOffset)
    (member : output ∈ SourceSplice.spliceOutputs saved inserted source) :
    output ∈ inserted ∨ ∃ sourceOutput ∈ source, output = .source sourceOutput := by
  induction saved generalizing source with
  | zero =>
      rw [SourceSplice.spliceOutputs] at member
      rcases List.mem_append.mp member with member | member
      · exact Or.inl member
      · obtain ⟨sourceOutput, sourceMember, rfl⟩ := List.mem_map.mp member
        exact Or.inr ⟨sourceOutput, sourceMember, rfl⟩
  | succ saved ih =>
      cases source with
      | nil => exact Or.inl member
      | cons head tail =>
          simp only [SourceSplice.spliceOutputs, List.mem_cons] at member
          rcases member with rfl | member
          · exact Or.inr ⟨head, List.mem_cons_self, rfl⟩
          · rcases ih tail member with insertedMember | ⟨sourceOutput, sourceMember, exact⟩
            · exact Or.inl insertedMember
            · exact Or.inr ⟨sourceOutput, List.mem_cons_of_mem _ sourceMember, exact⟩

theorem final_output_provenance {frame rootOffset}
    (splice : SourceSplice.Result frame rootOffset)
    (output : SourceSplice.FinalOutput frame rootOffset) (member : output ∈ splice.outputs) :
    (∃ sourceOutput ∈ splice.source.outputs, output = .source sourceOutput) ∨
    output = .allocation splice.prologue.allocation.encoding ∨
    (∃ entry ∈ splice.initialization.entries, output = .initialization entry) := by
  rw [splice.outputsExact] at member
  rcases spliceOutputs_member _ _ _ output member with inserted | source
  · simp only [List.mem_cons] at inserted
    rcases inserted with rfl | inserted
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp inserted
      exact Or.inr (Or.inr ⟨entry, entryMember, rfl⟩)
  · exact Or.inl source

theorem source_encoded_decodes {frame : SourceFrame.Result} {rootOffset : Nat}
    (output : SourceTemplates.Output frame rootOffset) (encoding : InsnEncoding)
    (encoded : output.template = .encoded encoding) (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest) := by
  cases output with
  | closed origin actual exact =>
      simp only [SourceTemplates.Output.template, SourceTemplates.Template.encoded.injEq] at encoded
      subst encoding
      exact X86ClosedEncoding.encode_decodes exact rest
  | store origin resolved exact =>
      simp only [SourceTemplates.Output.template, SourceTemplates.Template.encoded.injEq] at encoded
      subst encoding
      exact FrameStore.resolve?_encoding_decodes exact rest
  | load origin resolved exact =>
      simp only [SourceTemplates.Output.template, SourceTemplates.Template.encoded.injEq] at encoded
      subst encoding
      exact resolved.encoding_decodes rest
  | lea origin resolved exact =>
      simp only [SourceTemplates.Output.template, SourceTemplates.Template.encoded.injEq] at encoded
      subst encoding
      exact resolved.encoding_decodes rest
  | argument origin resolved exact =>
      simp only [SourceTemplates.Output.template, SourceTemplates.Template.encoded.injEq] at encoded
      subst encoding
      exact resolved.encoding_decodes rest
  | constant origin resolved exact =>
      simp only [SourceTemplates.Output.template, SourceTemplates.Template.encoded.injEq] at encoded
      subst encoding
      exact resolved.encoding_decodes rest
  | branch => cases encoded
  | ripAddress => cases encoded
  | ripCall => cases encoded
  | sizeOf32 => cases encoded

theorem prologue_allocation_decodes {frame rootOffset}
    (splice : SourceSplice.Result frame rootOffset) (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (splice.prologue.allocation.encoding.toBytes ++ rest) =
      .ok (splice.prologue.allocation.encoding, rest) :=
  FrameAllocation.encoding_decodes splice.prologue.allocation rest

theorem initializer_decodes {frame rootOffset}
    (splice : SourceSplice.Result frame rootOffset)
    (entry : SourceInitialization.Entry) (member : entry ∈ splice.initialization.entries)
    (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (entry.store.encoding.toBytes ++ rest) = .ok (entry.store.encoding, rest) :=
  splice.initialization.entry_encoding_decodes member rest

theorem final_encoded_decodes {frame rootOffset}
    (splice : SourceSplice.Result frame rootOffset)
    (output : SourceSplice.FinalOutput frame rootOffset) (member : output ∈ splice.outputs)
    (encoding : InsnEncoding)
    (encoded : output.template frame.saved.savedItems.length
      splice.initialization.entries.length = .encoded encoding)
    (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest) := by
  rcases final_output_provenance splice output member with
    ⟨sourceOutput, _, rfl⟩ | rfl | ⟨entry, entryMember, rfl⟩
  · cases ht : sourceOutput.template with
    | encoded actual =>
        simp [SourceSplice.FinalOutput.template, SourceSplice.translate, ht] at encoded
        subst encoding
        exact source_encoded_decodes sourceOutput actual ht rest
    | branch => simp [SourceSplice.FinalOutput.template, SourceSplice.translate, ht] at encoded
    | ripAddress => simp [SourceSplice.FinalOutput.template, SourceSplice.translate, ht] at encoded
    | ripCall => simp [SourceSplice.FinalOutput.template, SourceSplice.translate, ht] at encoded
    | sizeOf32 => simp [SourceSplice.FinalOutput.template, SourceSplice.translate, ht] at encoded
  · simp only [SourceSplice.FinalOutput.template,
      SourceSplice.FinalTemplate.encoded.injEq] at encoded
    subst encoding
    exact prologue_allocation_decodes splice rest
  · simp only [SourceSplice.FinalOutput.template,
      SourceSplice.FinalTemplate.encoded.injEq] at encoded
    subst encoding
    exact initializer_decodes splice entry entryMember rest

theorem source_final_output_decodes {frame rootOffset}
    (splice : SourceSplice.Result frame rootOffset) (sourceIndex : Nat)
    (sourceBound : sourceIndex < splice.source.outputs.length)
    (sourceOutput : SourceTemplates.Output frame rootOffset)
    (sourceAt : splice.source.outputs[sourceIndex]? = some sourceOutput)
    (encoding : InsnEncoding) (encoded : sourceOutput.template = .encoded encoding)
    (rest : Grass.Std.Logical.ByteSeq) :
    (splice.outputs[SourceSplice.sourceFinalIndex frame.saved.savedItems.length
      splice.initialization.entries.length sourceIndex]?).map
        (fun output => output.template frame.saved.savedItems.length
          splice.initialization.entries.length) = some (.encoded encoding) ∧
      decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest) := by
  constructor
  · rw [splice.source_output_at_final_index sourceIndex sourceBound, sourceAt]
    simp [SourceSplice.FinalOutput.template, SourceSplice.translate, encoded]
  · exact source_encoded_decodes sourceOutput encoding encoded rest

theorem allocation_final_output_decodes {frame rootOffset}
    (splice : SourceSplice.Result frame rootOffset) (rest : Grass.Std.Logical.ByteSeq) :
    splice.outputs[frame.saved.savedItems.length]? =
        some (.allocation splice.prologue.allocation.encoding) ∧
      decodeInsn (splice.prologue.allocation.encoding.toBytes ++ rest) =
        .ok (splice.prologue.allocation.encoding, rest) :=
  ⟨splice.allocation_at_boundary, prologue_allocation_decodes splice rest⟩

theorem initializer_final_output_decodes {frame rootOffset}
    (splice : SourceSplice.Result frame rootOffset) (index : Nat)
    (bounded : index < splice.initialization.entries.length)
    (rest : Grass.Std.Logical.ByteSeq) :
    splice.outputs[frame.saved.savedItems.length + 1 + index]? =
        (splice.initialization.entries[index]?).map .initialization ∧
      decodeInsn (splice.initialization.entries[index].store.encoding.toBytes ++ rest) =
        .ok (splice.initialization.entries[index].store.encoding, rest) := by
  refine ⟨splice.initializer_at index bounded, ?_⟩
  exact initializer_decodes splice splice.initialization.entries[index]
    (List.getElem_mem bounded) rest

end Grass.Assembly.SourceSpliceDecode
