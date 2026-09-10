import Grass.Assembly.SourceResolve

/-!
# Frame-memory selections from resolved source

The receipts here select exact entries of `SourceResolve.Result.outputs`. They
retain the corresponding source or initializer constructor, so later execution
proofs do not recover a memory operation merely by matching emitted bytes.
-/

namespace Grass.Assembly.SourceResolve

open Grass.ISA.X86

private theorem getElem?_bound {α : Type} {items : List α} {index : Nat} {item : α}
    (found : items[index]? = some item) : index < items.length :=
  (List.getElem?_eq_some_iff.mp found).choose

private theorem storeInput_eq_of_resolve? {layout : Grass.ABI.Win64.CallFrameLayout}
    {rootOffset : Nat} {env : Store32.SlotEnv} {input : Store32.Input}
    {store : Store32.Resolved}
    (success : Store32.resolve? layout rootOffset env input = some store) :
    store.input = input := by
  unfold Store32.resolve? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  rfl

/-- The resolved output at the same bounded index as an exact splice origin.
The value is selected by list indexing; the proof argument supplies only its bound. -/
def Result.outputAtOrigin {frame rootOffset} (source : Result frame rootOffset)
    {index : Nat} {origin : SourceSplice.FinalOutput frame rootOffset}
    (originAt : source.splice.outputs[index]? = some origin) :
    Output source.splice source.symbols source.codeBase :=
  source.outputs[index]'(by
    rw [source.countExact]
    exact getElem?_bound originAt)

/-- `outputAtOrigin` belongs to the exact resolved-output list. -/
theorem Result.outputAtOrigin_member {frame rootOffset} (source : Result frame rootOffset)
    {index : Nat} {origin : SourceSplice.FinalOutput frame rootOffset}
    (originAt : source.splice.outputs[index]? = some origin) :
    source.outputAtOrigin originAt ∈ source.outputs := by
  have spliceBound := getElem?_bound originAt
  have outputBound : index < source.outputs.length := by
    rw [source.countExact]
    exact spliceBound
  exact List.getElem_mem outputBound

/-- `outputAtOrigin` retains the splice index used to select it. -/
theorem Result.outputAtOrigin_index {frame rootOffset} (source : Result frame rootOffset)
    {index : Nat} {origin : SourceSplice.FinalOutput frame rootOffset}
    (originAt : source.splice.outputs[index]? = some origin) :
    (source.outputAtOrigin originAt).index = index := by
  have spliceBound := getElem?_bound originAt
  have outputBound : index < source.outputs.length := by
    rw [source.countExact]
    exact spliceBound
  have atIndex := congrArg (fun indices => indices[index]?) source.indicesExact
  simpa [Result.outputAtOrigin, List.getElem?_eq_getElem outputBound,
    List.getElem?_range, spliceBound] using atIndex

/-- `outputAtOrigin` retains the exact final-output origin, including its
constructor evidence. -/
theorem Result.outputAtOrigin_origin {frame rootOffset} (source : Result frame rootOffset)
    {index : Nat} {origin : SourceSplice.FinalOutput frame rootOffset}
    (originAt : source.splice.outputs[index]? = some origin) :
    (source.outputAtOrigin originAt).origin = origin := by
  have indexExact := source.outputAtOrigin_index originAt
  have selectedOrigin := (source.outputAtOrigin originAt).originAt
  rw [indexExact] at selectedOrigin
  exact Option.some.inj (selectedOrigin.symm.trans originAt)

/-- Select the resolved output whose stored origin occurs at `index` in the exact
splice output. -/
theorem Result.output_of_originAt {frame rootOffset} (source : Result frame rootOffset)
    {index : Nat} {origin : SourceSplice.FinalOutput frame rootOffset}
    (originAt : source.splice.outputs[index]? = some origin) :
    ∃ output : Output source.splice source.symbols source.codeBase,
      output ∈ source.outputs ∧ output.index = index ∧ output.origin = origin :=
  ⟨source.outputAtOrigin originAt, source.outputAtOrigin_member originAt,
    source.outputAtOrigin_index originAt, source.outputAtOrigin_origin originAt⟩

/-- An output whose exact origin has an encoded template uses that same encoding.
The proof follows `Output.templateExact` and `Output.detailExact`; it does not
compare byte lists. -/
theorem Output.encoding_eq_of_origin_encoded {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} {symbols : Symbols} {codeBase : Nat}
    (output : Output splice symbols codeBase) (encoding : InsnEncoding)
    (encoded : output.origin.template frame.saved.savedItems.length
      splice.initialization.entries.length = .encoded encoding) :
    output.encoding = encoding := by
  have templateExact : output.template = .encoded encoding :=
    output.templateExact.trans encoded
  cases hdetail : output.detail with
  | encoded =>
      have valid := output.detailExact
      rw [hdetail] at valid
      simp only [Detail.Valid] at valid
      rw [templateExact] at valid
      have same : encoding = output.encoding := by injection valid
      exact same.symm
  | branch kind targetIndex resolved =>
      have valid := output.detailExact
      rw [hdetail] at valid
      simp only [Detail.Valid] at valid
      rw [templateExact] at valid
      cases valid.1
  | ripStatic destination name symbol resolved =>
      have valid := output.detailExact
      rw [hdetail] at valid
      simp only [Detail.Valid] at valid
      obtain ⟨prototype, impossible⟩ := valid.1
      rw [templateExact] at impossible
      cases impossible
  | ripImport name symbol resolved =>
      have valid := output.detailExact
      rw [hdetail] at valid
      simp only [Detail.Valid] at valid
      obtain ⟨prototype, impossible⟩ := valid.1
      rw [templateExact] at impossible
      cases impossible
  | sizeOf32 destination name symbol =>
      have valid := output.detailExact
      rw [hdetail] at valid
      simp only [Detail.Valid] at valid
      obtain ⟨prototype, impossible⟩ := valid.2.1
      rw [templateExact] at impossible
      cases impossible

/-- A selected resolved store, with the exact source/initializer origin and the
primitive resolver receipt that determines its address and payload. -/
structure StoreSelection {frame rootOffset} (source : Result frame rootOffset) where
  output : Output source.splice source.symbols source.codeBase
  outputMember : output ∈ source.outputs
  store : Store32.Resolved
  input : Store32.Input
  primitiveExact : Store32.resolve? frame.layout rootOffset
    (SourceStore.slotEnv frame.slots) input = some store
  payloadExact : store.writeBytes = le32 input.value
  encodingExact : output.encoding = store.encoding
  origin :
    (∃ (sourceIndex : Nat) (item : X86ControlFlow.CodeItem)
        (success : FrameStore.resolve? frame rootOffset item = some store),
      source.splice.source.outputs[sourceIndex]? =
        some (.store item store success) ∧
      output.index = SourceSplice.sourceFinalIndex frame.saved.savedItems.length
        source.splice.initialization.entries.length sourceIndex ∧
      output.origin = .source (.store item store success) ∧
      ∃ (slot : String) (value : Nat),
        item.instruction.mnemonic = .mov ∧
        item.instruction.operands = [.symbol slot, .immediate value] ∧
        value < 2 ^ 32 ∧ input = ⟨slot, BitVec.ofNat 32 value⟩) ∨
    (∃ (index : Nat) (entry : SourceInitialization.Entry),
      source.splice.initialization.entries[index]? = some entry ∧
      entry.store = store ∧ input = SourceInitialization.inputOf entry.declaration ∧
      output.index = frame.saved.savedItems.length + 1 + index ∧
      output.origin = .initialization entry)

/-- Computably select an authored UInt32 store at its exact translated
source-output index. -/
def Result.storeSelectionOfSourceAt {frame rootOffset}
    (source : Result frame rootOffset) {sourceIndex : Nat} {item : X86ControlFlow.CodeItem}
    {store : Store32.Resolved}
    {success : FrameStore.resolve? frame rootOffset item = some store}
    (sourceAt : source.splice.source.outputs[sourceIndex]? =
      some (.store item store success)) :
    StoreSelection source := by
  have sourceBound := getElem?_bound sourceAt
  have originAt : source.splice.outputs[SourceSplice.sourceFinalIndex
      frame.saved.savedItems.length source.splice.initialization.entries.length sourceIndex]? =
      some (.source (.store item store success)) := by
    rw [source.splice.source_output_at_final_index sourceIndex sourceBound, sourceAt]
    rfl
  let output := source.outputAtOrigin originAt
  have outputMember := source.outputAtOrigin_member originAt
  have outputIndex := source.outputAtOrigin_index originAt
  have outputOrigin := source.outputAtOrigin_origin originAt
  have primitive : Store32.resolve? frame.layout rootOffset
      (SourceStore.slotEnv frame.slots) store.input = some store := by
    obtain ⟨_, slot, value, _, _, _, primitiveOriginal⟩ :=
      FrameStore.resolve?_source success
    have inputExact := storeInput_eq_of_resolve? primitiveOriginal
    simpa [inputExact] using primitiveOriginal
  have payload : store.writeBytes = le32 store.input.value :=
    Store32.writeBytes_of_resolve? primitive
  have encoding : output.encoding = store.encoding := by
    apply output.encoding_eq_of_origin_encoded
    rw [outputOrigin]
    rfl
  refine StoreSelection.mk output outputMember store store.input primitive payload encoding ?_
  left
  obtain ⟨_, slot, value, mnemonic, operands, valueBound, primitiveOriginal⟩ :=
    FrameStore.resolve?_source success
  have inputExact := storeInput_eq_of_resolve? primitiveOriginal
  exact ⟨sourceIndex, item, success, sourceAt, outputIndex, outputOrigin,
    slot, value, mnemonic, operands, valueBound, inputExact⟩

/-- The computable source-store selector has the store carried by its origin. -/
@[simp] theorem Result.storeSelectionOfSourceAt_store {frame rootOffset}
    (source : Result frame rootOffset) {sourceIndex : Nat} {item : X86ControlFlow.CodeItem}
    {store : Store32.Resolved}
    {success : FrameStore.resolve? frame rootOffset item = some store}
    (sourceAt : source.splice.source.outputs[sourceIndex]? =
      some (.store item store success)) :
    (source.storeSelectionOfSourceAt sourceAt).store = store := by
  simp [Result.storeSelectionOfSourceAt]

/-- Existential form of `storeSelectionOfSourceAt` for proposition-only callers. -/
theorem Result.storeSelection_of_sourceAt {frame rootOffset}
    (source : Result frame rootOffset) {sourceIndex : Nat} {item : X86ControlFlow.CodeItem}
    {store : Store32.Resolved}
    {success : FrameStore.resolve? frame rootOffset item = some store}
    (sourceAt : source.splice.source.outputs[sourceIndex]? =
      some (.store item store success)) :
    ∃ selection : StoreSelection source, selection.store = store :=
  ⟨source.storeSelectionOfSourceAt sourceAt, rfl⟩

/-- Computably select a generated local initializer from its exact list lookup. -/
def Result.storeSelectionOfInitializerAt {frame rootOffset}
    (source : Result frame rootOffset) (index : Nat) (entry : SourceInitialization.Entry)
    (entryAt : source.splice.initialization.entries[index]? = some entry) :
    StoreSelection source := by
  have entryBound := getElem?_bound entryAt
  have originAt : source.splice.outputs[frame.saved.savedItems.length + 1 + index]? =
      some (.initialization entry) := by
    rw [source.splice.initializer_at index entryBound, entryAt]
    rfl
  let output := source.outputAtOrigin originAt
  have outputMember := source.outputAtOrigin_member originAt
  have outputIndex := source.outputAtOrigin_index originAt
  have outputOrigin := source.outputAtOrigin_origin originAt
  have member : entry ∈ source.splice.initialization.entries :=
    List.mem_of_getElem? entryAt
  have primitive : Store32.resolve? frame.layout rootOffset
      (SourceStore.slotEnv frame.slots) (SourceInitialization.inputOf entry.declaration) =
      some entry.store := by
    simpa [source.splice.initializationFrame, source.splice.initializationRoot] using
      (source.splice.initialization.entry_exact member).2
  have payload := Store32.writeBytes_of_resolve? primitive
  have encoding : output.encoding = entry.store.encoding := by
    apply output.encoding_eq_of_origin_encoded
    rw [outputOrigin]
    rfl
  exact StoreSelection.mk output outputMember entry.store
    (SourceInitialization.inputOf entry.declaration) primitive payload encoding
    (Or.inr ⟨index, entry, entryAt, rfl, rfl, outputIndex, outputOrigin⟩)

/-- The computable initializer selector has the store carried by its entry. -/
@[simp] theorem Result.storeSelectionOfInitializerAt_store {frame rootOffset}
    (source : Result frame rootOffset) (index : Nat) (entry : SourceInitialization.Entry)
    (entryAt : source.splice.initialization.entries[index]? = some entry) :
    (source.storeSelectionOfInitializerAt index entry entryAt).store = entry.store := by
  simp [Result.storeSelectionOfInitializerAt]

/-- Select a generated local initializer from membership when only a proposition
receipt is needed. -/
theorem Result.storeSelection_of_initializer {frame rootOffset}
    (source : Result frame rootOffset) {entry : SourceInitialization.Entry}
    (member : entry ∈ source.splice.initialization.entries) :
    ∃ selection : StoreSelection source, selection.store = entry.store := by
  obtain ⟨index, entryAt⟩ := List.mem_iff_getElem?.mp member
  exact ⟨source.storeSelectionOfInitializerAt index entry entryAt,
    source.storeSelectionOfInitializerAt_store index entry entryAt⟩

/-- An exact resolved UInt32 load selected from the authored source outputs. -/
structure LoadSelection {frame rootOffset} (source : Result frame rootOffset) where
  output : Output source.splice source.symbols source.codeBase
  outputMember : output ∈ source.outputs
  result : FrameLoad.Result
  item : X86ControlFlow.CodeItem
  success : FrameLoad.resolve? frame rootOffset item = some result
  sourceIndex : Nat
  sourceAt : source.splice.source.outputs[sourceIndex]? = some (.load item result success)
  outputIndex : output.index = SourceSplice.sourceFinalIndex frame.saved.savedItems.length
    source.splice.initialization.entries.length sourceIndex
  originExact : output.origin = .source (.load item result success)
  encodingExact : output.encoding = result.encoding

/-- Computably recover a load selection from its exact source-output lookup. -/
def Result.loadSelectionOfSourceAt {frame rootOffset} (source : Result frame rootOffset)
    {sourceIndex : Nat} {item : X86ControlFlow.CodeItem} {result : FrameLoad.Result}
    {success : FrameLoad.resolve? frame rootOffset item = some result}
    (sourceAt : source.splice.source.outputs[sourceIndex]? = some (.load item result success)) :
    LoadSelection source := by
  have sourceBound := getElem?_bound sourceAt
  have originAt : source.splice.outputs[SourceSplice.sourceFinalIndex
      frame.saved.savedItems.length source.splice.initialization.entries.length sourceIndex]? =
      some (.source (.load item result success)) := by
    rw [source.splice.source_output_at_final_index sourceIndex sourceBound, sourceAt]
    rfl
  let output := source.outputAtOrigin originAt
  have outputMember := source.outputAtOrigin_member originAt
  have outputIndex := source.outputAtOrigin_index originAt
  have originExact := source.outputAtOrigin_origin originAt
  have encodingExact : output.encoding = result.encoding := by
    apply output.encoding_eq_of_origin_encoded
    rw [originExact]
    rfl
  exact LoadSelection.mk output outputMember result item success sourceIndex sourceAt
    outputIndex originExact encodingExact

/-- The computable load selector has the result carried by its source origin. -/
@[simp] theorem Result.loadSelectionOfSourceAt_result {frame rootOffset}
    (source : Result frame rootOffset) {sourceIndex : Nat} {item : X86ControlFlow.CodeItem}
    {result : FrameLoad.Result}
    {success : FrameLoad.resolve? frame rootOffset item = some result}
    (sourceAt : source.splice.source.outputs[sourceIndex]? = some (.load item result success)) :
    (source.loadSelectionOfSourceAt sourceAt).result = result := by
  simp [Result.loadSelectionOfSourceAt]

/-- Existential form of `loadSelectionOfSourceAt`. -/
theorem Result.loadSelection_of_sourceAt {frame rootOffset} (source : Result frame rootOffset)
    {sourceIndex : Nat} {item : X86ControlFlow.CodeItem} {result : FrameLoad.Result}
    {success : FrameLoad.resolve? frame rootOffset item = some result}
    (sourceAt : source.splice.source.outputs[sourceIndex]? = some (.load item result success)) :
    ∃ selection : LoadSelection source, selection.result = result :=
  ⟨source.loadSelectionOfSourceAt sourceAt,
    source.loadSelectionOfSourceAt_result sourceAt⟩

/-- An exact resolved stack-argument store selected from authored source outputs. -/
structure ArgumentSelection {frame rootOffset} (source : Result frame rootOffset) where
  output : Output source.splice source.symbols source.codeBase
  outputMember : output ∈ source.outputs
  result : FrameArgument.Result
  item : X86ControlFlow.CodeItem
  success : FrameArgument.resolve? frame rootOffset item = some result
  sourceIndex : Nat
  sourceAt : source.splice.source.outputs[sourceIndex]? = some (.argument item result success)
  outputIndex : output.index = SourceSplice.sourceFinalIndex frame.saved.savedItems.length
    source.splice.initialization.entries.length sourceIndex
  originExact : output.origin = .source (.argument item result success)
  encodingExact : output.encoding = result.encoding

/-- Computably recover an argument selection from its exact source-output lookup. -/
def Result.argumentSelectionOfSourceAt {frame rootOffset}
    (source : Result frame rootOffset) {sourceIndex : Nat} {item : X86ControlFlow.CodeItem}
    {result : FrameArgument.Result}
    {success : FrameArgument.resolve? frame rootOffset item = some result}
    (sourceAt : source.splice.source.outputs[sourceIndex]? =
      some (.argument item result success)) :
    ArgumentSelection source := by
  have sourceBound := getElem?_bound sourceAt
  have originAt : source.splice.outputs[SourceSplice.sourceFinalIndex
      frame.saved.savedItems.length source.splice.initialization.entries.length sourceIndex]? =
      some (.source (.argument item result success)) := by
    rw [source.splice.source_output_at_final_index sourceIndex sourceBound, sourceAt]
    rfl
  let output := source.outputAtOrigin originAt
  have outputMember := source.outputAtOrigin_member originAt
  have outputIndex := source.outputAtOrigin_index originAt
  have originExact := source.outputAtOrigin_origin originAt
  have encodingExact : output.encoding = result.encoding := by
    apply output.encoding_eq_of_origin_encoded
    rw [originExact]
    rfl
  exact ArgumentSelection.mk output outputMember result item success sourceIndex sourceAt
    outputIndex originExact encodingExact

/-- The computable argument selector has the result carried by its source origin. -/
@[simp] theorem Result.argumentSelectionOfSourceAt_result {frame rootOffset}
    (source : Result frame rootOffset) {sourceIndex : Nat} {item : X86ControlFlow.CodeItem}
    {result : FrameArgument.Result}
    {success : FrameArgument.resolve? frame rootOffset item = some result}
    (sourceAt : source.splice.source.outputs[sourceIndex]? =
      some (.argument item result success)) :
    (source.argumentSelectionOfSourceAt sourceAt).result = result := by
  simp [Result.argumentSelectionOfSourceAt]

/-- Existential form of `argumentSelectionOfSourceAt`. -/
theorem Result.argumentSelection_of_sourceAt {frame rootOffset}
    (source : Result frame rootOffset) {sourceIndex : Nat} {item : X86ControlFlow.CodeItem}
    {result : FrameArgument.Result}
    {success : FrameArgument.resolve? frame rootOffset item = some result}
    (sourceAt : source.splice.source.outputs[sourceIndex]? =
      some (.argument item result success)) :
    ∃ selection : ArgumentSelection source, selection.result = result :=
  ⟨source.argumentSelectionOfSourceAt sourceAt,
    source.argumentSelectionOfSourceAt_result sourceAt⟩

end Grass.Assembly.SourceResolve
