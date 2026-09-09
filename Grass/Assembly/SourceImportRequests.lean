import Grass.Artifact.PE.Description
import Grass.Assembly.SourceSplice
import Grass.Platform.Win32.Signatures
import Grass.Std.Logical.Text

/-! Checked source import request builder. It selects no concrete DLL: the
library name is an explicit input. PE layout and serialization remain downstream. -/
namespace Grass.Assembly.SourceImportRequests

open Grass.Artifact.PE Grass.Platform.Win32.Signatures Grass.Std.Logical

def importName? {frame rootOffset} (savedCount initializerCount : Nat)
    (output : SourceSplice.FinalOutput frame rootOffset) : Option String :=
  match output.template savedCount initializerCount with
  | .ripCall name _ => some name
  | _ => none

def rawImportNames {frame rootOffset} (splice : SourceSplice.Result frame rootOffset) :
    List String :=
  splice.outputs.filterMap
    (importName? frame.saved.savedItems.length splice.initialization.entries.length)

/-- First-occurrence order from the final source splice, with repeated calls removed. -/
def sourceImportNames {frame rootOffset} (splice : SourceSplice.Result frame rootOffset) :
    List String := (rawImportNames splice).eraseDups

theorem sourceImportNames_mem_iff {frame rootOffset}
    (splice : SourceSplice.Result frame rootOffset) (name : String) :
    name ∈ sourceImportNames splice ↔
      ∃ output ∈ splice.outputs,
        ∃ prototype, output.template frame.saved.savedItems.length
          splice.initialization.entries.length = .ripCall name prototype := by
  rw [sourceImportNames, List.mem_eraseDups, rawImportNames, List.mem_filterMap]
  constructor
  · rintro ⟨output, member, exact⟩
    unfold importName? at exact
    split at exact <;> try contradiction
    rename_i foundName prototype templateExact
    cases exact
    exact ⟨output, member, prototype, templateExact⟩
  · rintro ⟨output, member, prototype, templateExact⟩
    refine ⟨output, member, ?_⟩
    simp [importName?, templateExact]

structure Entry where
  private mk ::
  sourceName : String
  api : Api
  sourceExact : resolveImport? sourceName = some api
  nativeSymbol : ImportSymbol
  nativeExact : nativeSymbol.name = Text.utf8 (apiName api)

def resolveName? (sourceName : String) : Option Entry := do
  match exact : resolveImport? sourceName with
  | none => none
  | some api => some ⟨sourceName, api, exact, ⟨Text.utf8 (apiName api)⟩, rfl⟩

theorem resolveName?_source {sourceName : String} {entry : Entry}
    (success : resolveName? sourceName = some entry) : entry.sourceName = sourceName := by
  unfold resolveName? at success
  split at success <;> try contradiction
  cases success
  rfl

theorem Entry.source_to_native (entry : Entry) :
    importName entry.api = entry.sourceName ∧
      entry.nativeSymbol.name = Text.utf8 (apiName entry.api) :=
  ⟨resolveImport?_exact entry.sourceExact, entry.nativeExact⟩

private def resolveNames? : List String → Option (List Entry)
  | [] => some []
  | name :: names => do pure ((← resolveName? name) :: (← resolveNames? names))

private theorem resolveNames?_names {names : List String} {entries : List Entry}
    (success : resolveNames? names = some entries) : entries.map Entry.sourceName = names := by
  induction names generalizing entries with
  | nil => simp [resolveNames?] at success; cases success; rfl
  | cons name names ih =>
      cases headExact : resolveName? name with
      | none => simp [resolveNames?, headExact] at success
      | some head =>
          cases tailExact : resolveNames? names with
          | none => simp [resolveNames?, headExact, tailExact] at success
          | some tail =>
              simp [resolveNames?, headExact, tailExact] at success
              cases success
              simp [resolveName?_source headExact, ih tailExact]

structure Result {frame : SourceFrame.Result} {rootOffset : Nat}
    (splice : SourceSplice.Result frame rootOffset) where
  private mk ::
  libraryName : String
  sourceNames : List String
  sourceNamesExact : sourceNames = sourceImportNames splice
  sourceNamesUnique : sourceNames.Nodup
  entries : List Entry
  entriesExact : resolveNames? sourceNames = some entries
  library : ImportLibrary
  libraryExact : library =
    { name := Text.utf8 libraryName
      symbols := Vec.fromList (entries.map Entry.nativeSymbol) }

def resolve? {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    (libraryName : String) : Option (Result splice) := do
  let names := sourceImportNames splice
  if unique : names.Nodup then
    match exact : resolveNames? names with
    | none => none
    | some entries => some ⟨libraryName, names, rfl, unique, entries, exact,
        { name := Text.utf8 libraryName
          symbols := Vec.fromList (entries.map Entry.nativeSymbol) }, rfl⟩
  else none

theorem resolve?_inputs {frame rootOffset} {splice : SourceSplice.Result frame rootOffset}
    {libraryName : String} {result : Result splice}
    (success : resolve? splice libraryName = some result) :
    result.libraryName = libraryName := by
  unfold resolve? at success
  dsimp only at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  rfl

theorem Result.entry_order {frame rootOffset} {splice : SourceSplice.Result frame rootOffset}
    (result : Result splice) : result.entries.map Entry.sourceName = result.sourceNames :=
  resolveNames?_names result.entriesExact

theorem Result.source_name_covered {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} (result : Result splice)
    {output : SourceSplice.FinalOutput frame rootOffset} (member : output ∈ splice.outputs)
    {name : String} {prototype : Grass.ISA.X86.InsnEncoding}
    (templateExact : output.template frame.saved.savedItems.length
      splice.initialization.entries.length = .ripCall name prototype) :
    name ∈ result.sourceNames := by
  rw [result.sourceNamesExact]
  exact (sourceImportNames_mem_iff splice name).2 ⟨output, member, prototype, templateExact⟩

theorem Result.entry_has_source {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} (result : Result splice)
    {entry : Entry} (member : entry ∈ result.entries) :
    ∃ output ∈ splice.outputs, ∃ prototype,
      output.template frame.saved.savedItems.length splice.initialization.entries.length =
        .ripCall entry.sourceName prototype := by
  have nameMember : entry.sourceName ∈ result.sourceNames := by
    rw [← result.entry_order]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [result.sourceNamesExact] at nameMember
  exact (sourceImportNames_mem_iff splice entry.sourceName).1 nameMember

theorem Result.library_name {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} (result : Result splice) :
    result.library.name = Text.utf8 result.libraryName := by rw [result.libraryExact]

theorem Result.library_symbols {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} (result : Result splice) :
    result.library.symbols.toList = result.entries.map Entry.nativeSymbol := by
  rw [result.libraryExact]

end Grass.Assembly.SourceImportRequests
