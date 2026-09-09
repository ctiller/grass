import Grass.Artifact.PE.Validation
import Grass.Assembly.SourceResolve
import Grass.Platform.Win32.Signatures
import Grass.Std.Logical.Text

/-! Checked bridge from selected Win32 source imports to the IAT RVAs of one
checked PE plan. The library identity is an explicit input. No import layout or
serialization is reproduced here. -/
namespace Grass.Assembly.SourceImportBindings

open Grass.Artifact.PE Grass.Platform.Win32.Signatures Grass.Std.Logical

def libraryCandidates (plan : ImagePlan) (libraryName : String) :
    List (ImportLibrary × Nat) :=
  plan.layout.requested.imports.toList.zipIdx.filter
    (fun pair => pair.1.name == Text.utf8 libraryName)

structure LibraryBinding (plan : ImagePlan) where
  private mk ::
  requestedName : String
  library : ImportLibrary
  libraryIndex : Nat
  candidatesExact : libraryCandidates plan requestedName = [(library, libraryIndex)]

def resolveLibrary? (plan : ImagePlan) (libraryName : String) : Option (LibraryBinding plan) :=
  match exact : libraryCandidates plan libraryName with
  | [(library, index)] => some ⟨libraryName, library, index, exact⟩
  | _ => none

theorem resolveLibrary?_name {plan : ImagePlan} {libraryName : String}
    {binding : LibraryBinding plan}
    (success : resolveLibrary? plan libraryName = some binding) :
    binding.requestedName = libraryName := by
  unfold resolveLibrary? at success
  split at success <;> try contradiction
  cases success
  rfl

theorem LibraryBinding.name_bytes {plan : ImagePlan} (binding : LibraryBinding plan) :
    binding.library.name = Text.utf8 binding.requestedName := by
  have member : (binding.library, binding.libraryIndex) ∈
      libraryCandidates plan binding.requestedName := by
    rw [binding.candidatesExact]
    simp
  simpa using (List.mem_filter.mp member).2

theorem LibraryBinding.requested_member {plan : ImagePlan} (binding : LibraryBinding plan) :
    (binding.library, binding.libraryIndex) ∈
      plan.layout.requested.imports.toList.zipIdx := by
  have member : (binding.library, binding.libraryIndex) ∈
      libraryCandidates plan binding.requestedName := by
    rw [binding.candidatesExact]
    simp
  exact (List.mem_filter.mp member).1

def symbolCandidates {plan : ImagePlan} (library : LibraryBinding plan) (api : Api) :
    List (ImportSymbol × Nat) :=
  library.library.symbols.toList.zipIdx.filter
    (fun pair => pair.1.name == Text.utf8 (apiName api))

structure Binding (plan : ImagePlan) (library : LibraryBinding plan) where
  private mk ::
  sourceName : String
  api : Api
  sourceNameExact : resolveImport? sourceName = some api
  symbol : ImportSymbol
  symbolIndex : Nat
  symbolCandidatesExact : symbolCandidates library api = [(symbol, symbolIndex)]
  iatRva : Nat
  iatExact : plan.layout.importAddressRva? library.libraryIndex symbolIndex = some iatRva

def Binding.sourceImport {plan : ImagePlan} {library : LibraryBinding plan}
    (binding : Binding plan library) : SourceResolve.ImportSymbol :=
  ⟨binding.sourceName, binding.iatRva⟩

def resolveOne? {plan : ImagePlan} (library : LibraryBinding plan)
    (sourceName : String) : Option (Binding plan library) := do
  match sourceExact : resolveImport? sourceName with
  | none => none
  | some api =>
    match symbolExact : symbolCandidates library api with
    | [(symbol, symbolIndex)] =>
      match iatExact : plan.layout.importAddressRva? library.libraryIndex symbolIndex with
      | none => none
      | some iatRva => some ⟨sourceName, api, sourceExact, symbol, symbolIndex,
          symbolExact, iatRva, iatExact⟩
    | _ => none

theorem resolveOne?_source {plan : ImagePlan} {library : LibraryBinding plan}
    {sourceName : String} {binding : Binding plan library}
    (success : resolveOne? library sourceName = some binding) :
    binding.sourceName = sourceName := by
  unfold resolveOne? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  rfl

private def resolveNames? {plan : ImagePlan} (library : LibraryBinding plan) :
    List String → Option (List (Binding plan library))
  | [] => some []
  | name :: names => do
      pure ((← resolveOne? library name) :: (← resolveNames? library names))

structure Result (plan : ImagePlan) where
  private mk ::
  library : LibraryBinding plan
  requestedNames : List String
  namesUnique : requestedNames.Nodup
  bindings : List (Binding plan library)
  bindingsExact : resolveNames? library requestedNames = some bindings

def resolve? (plan : ImagePlan) (libraryName : String)
    (requestedNames : List String) : Option (Result plan) := do
  if unique : requestedNames.Nodup then
    let library ← resolveLibrary? plan libraryName
    match exact : resolveNames? library requestedNames with
    | none => none
    | some bindings => some ⟨library, requestedNames, unique, bindings, exact⟩
  else none

theorem resolve?_inputs {plan : ImagePlan} {libraryName : String}
    {requestedNames : List String} {result : Result plan}
    (success : resolve? plan libraryName requestedNames = some result) :
    result.library.requestedName = libraryName ∧ result.requestedNames = requestedNames := by
  unfold resolve? at success
  split at success <;> try contradiction
  generalize libraryEq : resolveLibrary? plan libraryName = libraryOption at success
  cases libraryOption with
  | none => simp at success
  | some library =>
      simp at success
      split at success <;> try contradiction
      cases success
      exact ⟨resolveLibrary?_name libraryEq, rfl⟩

private theorem resolveNames?_names {plan : ImagePlan} {library : LibraryBinding plan}
    {names : List String} {bindings : List (Binding plan library)}
    (success : resolveNames? library names = some bindings) :
    bindings.map Binding.sourceName = names := by
  induction names generalizing bindings with
  | nil => simp [resolveNames?] at success; cases success; rfl
  | cons name names ih =>
      cases headExact : resolveOne? library name with
      | none => simp [resolveNames?, headExact] at success
      | some head =>
          cases tailExact : resolveNames? library names with
          | none => simp [resolveNames?, headExact, tailExact] at success
          | some tail =>
              simp [resolveNames?, headExact, tailExact] at success
              cases success
              simp [resolveOne?_source headExact, ih tailExact]

theorem Result.input_order {plan : ImagePlan} (result : Result plan) :
    result.bindings.map Binding.sourceName = result.requestedNames :=
  resolveNames?_names result.bindingsExact

theorem Binding.source_name {plan : ImagePlan} {library : LibraryBinding plan}
    (binding : Binding plan library) : binding.sourceImport.name = binding.sourceName := rfl

theorem Binding.source_iat_rva {plan : ImagePlan} {library : LibraryBinding plan}
    (binding : Binding plan library) : binding.sourceImport.iatAddress = binding.iatRva := rfl

theorem Binding.native_name {plan : ImagePlan} {library : LibraryBinding plan}
    (binding : Binding plan library) : importName binding.api = binding.sourceName :=
  resolveImport?_exact binding.sourceNameExact

theorem Binding.symbol_name_bytes {plan : ImagePlan} {library : LibraryBinding plan}
    (binding : Binding plan library) :
    binding.symbol.name = Text.utf8 (apiName binding.api) := by
  have member : (binding.symbol, binding.symbolIndex) ∈
      symbolCandidates library binding.api := by
    rw [binding.symbolCandidatesExact]
    simp
  simpa using (List.mem_filter.mp member).2

theorem Binding.symbol_member {plan : ImagePlan} {library : LibraryBinding plan}
    (binding : Binding plan library) :
    (binding.symbol, binding.symbolIndex) ∈ library.library.symbols.toList.zipIdx := by
  have member : (binding.symbol, binding.symbolIndex) ∈
      symbolCandidates library binding.api := by
    rw [binding.symbolCandidatesExact]
    simp
  exact (List.mem_filter.mp member).1

def Result.sourceImports {plan : ImagePlan} (result : Result plan) :
    List SourceResolve.ImportSymbol := result.bindings.map Binding.sourceImport

theorem Result.source_import_names {plan : ImagePlan} (result : Result plan) :
    result.sourceImports.map SourceResolve.ImportSymbol.name = result.requestedNames := by
  simpa [Result.sourceImports, List.map_map, Binding.sourceImport, Function.comp_def]
    using result.input_order

theorem Result.source_import_names_unique {plan : ImagePlan} (result : Result plan) :
    (result.sourceImports.map SourceResolve.ImportSymbol.name).Nodup := by
  rw [result.source_import_names]
  exact result.namesUnique

end Grass.Assembly.SourceImportBindings
