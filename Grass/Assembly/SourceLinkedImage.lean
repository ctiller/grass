import Grass.Assembly.SourceImage
import Grass.Assembly.SourceStaticBindings
import Grass.Assembly.SourceImportBindings
import Grass.Assembly.SourceImportRequests
import Grass.Artifact.PE.ImageWriter

import Grass.Assembly.SourceUnwindPrefix
import Grass.Artifact.PE.ExceptionBinding

/-! Source-derived code, static objects, imports and unwind metadata in one
checked PE plan. `Result` retains final bytes, symbol bindings and a present
exception table. Execution, semantic unwind reversal and specification
correspondence remain separate obligations; this is not an emission certificate. -/

namespace Grass.Assembly.SourceLinkedImage
open Grass.Artifact.PE Grass.Std.Logical
structure Sections where
  codeName : SectionName
  codeCharacteristics : BitVec 32
  pdataName : SectionName
  xdataName : SectionName

def pdataIndex : Nat := 2
def xdataIndex : Nat := 3

private def placeholderFunction : ResolvedRuntimeFunction :=
  ⟨0, 0, 0, Vec.empty, Vec.empty⟩

/-- The provisional table has the exact measured width of one serializer output. -/
def placeholderTable : Grass.Std.Logical.ByteArray := writeRuntimeFunction placeholderFunction
def tableSize : Nat := placeholderTable.length

def codeExtent (codeLength : Nat) : SectionExtent := ⟨⟨0, 0⟩, codeLength⟩
def tableExtent : SectionExtent := ⟨⟨pdataIndex, 0⟩, tableSize⟩
def unwindExtent (unwindLength : Nat) : SectionExtent :=
  ⟨⟨xdataIndex, 0⟩, unwindLength⟩

def runtimeBinding (codeLength : Nat) {prologue : SourcePrologue.Result}
    (unwind : SourceUnwind.Result prologue) : RuntimeFunctionBinding :=
  ⟨codeExtent codeLength, unwindExtent unwind.bytes.length, unwind.bytes⟩

def exceptionDescription (codeLength : Nat) {prologue : SourcePrologue.Result}
    (unwind : SourceUnwind.Result prologue) : ExceptionTableDescription :=
  ⟨tableExtent, Vec.singleton (runtimeBinding codeLength unwind)⟩

def description {table : StaticObjects.Table} (sections : Sections)
    (statics : StaticSection.Layout table) (imports : Vec ImportLibrary)
    (code pdata xdata : Grass.Std.Logical.ByteArray)
    (exceptions : Option ExceptionTableDescription) : ExecutableImageDescription :=
  { entryPoint := ⟨0, 0⟩
    sections := Vec.fromList [⟨sections.codeName, code, sections.codeCharacteristics⟩,
      statics.rawSection,
      ⟨sections.pdataName, pdata, sectionReadable ||| sectionInitializedData⟩,
      ⟨sections.xdataName, xdata, sectionReadable ||| sectionInitializedData⟩]
    imports
    exceptionTable := exceptions }

/-- Both symbol populations refer to the same checked image and selected import request. -/
structure BoundSymbols (plan : ImagePlan) {table : StaticObjects.Table}
    (statics : StaticSection.Layout table) (libraryName : String) (names : List String) where
  staticBindings : SourceStaticBindings.Result plan statics 1
  importBindings : SourceImportBindings.Result plan
  libraryExact : importBindings.library.requestedName = libraryName
  namesExact : importBindings.requestedNames = names

def BoundSymbols.symbols {plan : ImagePlan} {table : StaticObjects.Table}
    {statics : StaticSection.Layout table} {libraryName : String} {names : List String}
    (bindings : BoundSymbols plan statics libraryName names) :
    SourceResolve.Symbols :=
  SourceResolve.Symbols.checked bindings.staticBindings.sourceSymbols
    bindings.importBindings.sourceImports bindings.staticBindings.uniqueNames
    bindings.importBindings.source_import_names_unique

private theorem prepareImage_requested {requested : ExecutableImageDescription}
    {plan : ImagePlan} (prepared : prepareImage requested = .ok plan) :
    plan.layout.requested = requested := by
  unfold prepareImage at prepared
  cases layoutEq : resolveImageLayout? requested with
  | none => simp [layoutEq] at prepared
  | some layout =>
      simp only [layoutEq] at prepared
      split at prepared
      · cases prepared
        unfold resolveImageLayout? at layoutEq
        split at layoutEq <;> try contradiction
        dsimp only at layoutEq
        split at layoutEq <;> try contradiction
        cases layoutEq
        rfl
      · simp at prepared

/-- One final checked plan retains the existing source/image/binding checks and
has a present, validated exception table for the exact source-derived unwind bytes. -/
structure Result {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    {table : StaticObjects.Table} (statics : StaticSection.Layout table)
    (sections : Sections) (requests : SourceImportRequests.Result splice) where
  unwind : SourceUnwind.Result splice.prologue
  source : SourceResolve.Result frame rootOffset
  sourceExact : source.splice = splice
  exceptionTable : ExceptionTableDescription
  exceptionExact : exceptionTable = exceptionDescription source.bytes.length unwind
  provisionalFunction : ResolvedRuntimeFunction
  tableBytes : Grass.Std.Logical.ByteArray
  tableBytesExact : tableBytes = writeRuntimeFunction provisionalFunction
  plan : ImagePlan
  prepared : prepareImage (description sections statics (Vec.singleton requests.library)
    source.bytes tableBytes unwind.bytes (some exceptionTable)) = .ok plan
  requestedException : plan.layout.requested.exceptionTable = some exceptionTable
  code : SourceImage.CodeSection source plan 0
  pdata : PlacedSection
  pdataSelected : plan.layout.placed.get? pdataIndex = some pdata
  pdataBytesExact : pdata.source.contents = tableBytes
  xdata : PlacedSection
  xdataSelected : plan.layout.placed.get? xdataIndex = some xdata
  xdataBytesExact : xdata.source.contents = unwind.bytes
  bindings : BoundSymbols plan statics requests.libraryName requests.sourceNames
  staticsExact : source.symbols.statics = bindings.staticBindings.sourceSymbols
  importsExact : source.symbols.imports = bindings.importBindings.sourceImports

inductive BuildError where
  | unwind
  | prototypeImage (cause : String)
  | prototypeCodeBase
  | prototypeStaticBinding
  | prototypeImportBinding
  | sourceResolution
  | metadataLayout
  | runtimeResolution
  | finalImage (cause : String)
  | pdataSelection
  | pdataBytes
  | xdataSelection
  | xdataBytes
  | finalCodeBinding
  | finalStaticBinding
  | finalImportBinding
  | finalStaticsMismatch
  | finalImportsMismatch
deriving Repr, DecidableEq

private def requireSome {α : Type} (error : BuildError) : Option α → Except BuildError α
  | none => .error error
  | some value => .ok value

private def prepare (phase : String → BuildError) (requested : ExecutableImageDescription) :
    Except BuildError ImagePlan :=
  match prepareImage requested with
  | .error cause => .error (phase cause)
  | .ok plan => .ok plan

private def bindSymbols (staticError importError : BuildError) (plan : ImagePlan)
    {table : StaticObjects.Table} (statics : StaticSection.Layout table)
    (libraryName : String) (names : List String) :
    Except BuildError (BoundSymbols plan statics libraryName names) := do
  let staticBindings ← requireSome staticError (SourceStaticBindings.resolve? plan statics 1)
  match exact : SourceImportBindings.resolve? plan libraryName names with
  | none => .error importError
  | some importBindings =>
      .ok ⟨staticBindings, importBindings, (SourceImportBindings.resolve?_inputs exact).1,
        (SourceImportBindings.resolve?_inputs exact).2⟩

/-- Erase only binding diagnostics from the shared binding implementation. -/
def bindSymbols? (plan : ImagePlan) {table : StaticObjects.Table}
    (statics : StaticSection.Layout table) (libraryName : String) (names : List String) :
    Option (BoundSymbols plan statics libraryName names) :=
  (bindSymbols .prototypeStaticBinding .prototypeImportBinding plan statics libraryName names).toOption
/-- The single phase-bearing construction pipeline. -/
def buildExcept {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    {table : StaticObjects.Table} (statics : StaticSection.Layout table)
    (sections : Sections) (requests : SourceImportRequests.Result splice) :
    Except BuildError (Result splice statics sections requests) := do
  let unwind ← requireSome .unwind (SourceUnwind.prepare? splice.prologue)
  let imports := Vec.singleton requests.library
  let prototypeDescription := description sections statics imports
    (Vec.replicate splice.finalSizes.sum 0) placeholderTable unwind.bytes none
  let prototype ← prepare .prototypeImage prototypeDescription
  let base ← requireSome .prototypeCodeBase (prototype.resolveSectionBase? 0)
  let preliminary ← bindSymbols .prototypeStaticBinding .prototypeImportBinding
    prototype statics requests.libraryName requests.sourceNames
  match resolved : SourceResolve.resolve? splice preliminary.symbols base.rva with
  | none => .error .sourceResolution
  | some source =>
    let exceptionTable := exceptionDescription source.bytes.length unwind
    let metadataDescription := description sections statics imports source.bytes
      placeholderTable unwind.bytes (some exceptionTable)
    match provisionalLayout : resolveImageLayout? metadataDescription with
    | none => .error .metadataLayout
    | some layout =>
      match runtimeExact : resolveRuntimeFunction? layout.placed
          (runtimeBinding source.bytes.length unwind) with
      | none => .error .runtimeResolution
      | some provisionalFunction =>
        let tableBytes := writeRuntimeFunction provisionalFunction
        let finalDescription := description sections statics imports source.bytes
          tableBytes unwind.bytes (some exceptionTable)
        match prepared : prepareImage finalDescription with
        | .error cause => .error (.finalImage cause)
        | .ok plan =>
          match pdataSelected : plan.layout.placed.get? pdataIndex with
          | none => .error .pdataSelection
          | some pdata =>
            if pdataBytesExact : pdata.source.contents = tableBytes then
              match xdataSelected : plan.layout.placed.get? xdataIndex with
              | none => .error .xdataSelection
              | some xdata => do
                if xdataBytesExact : xdata.source.contents = unwind.bytes then
                  let code ← requireSome .finalCodeBinding (SourceImage.bindCode? source plan 0)
                  let bindings ← bindSymbols .finalStaticBinding .finalImportBinding plan statics
                    requests.libraryName requests.sourceNames
                  if staticsExact : source.symbols.statics =
                      bindings.staticBindings.sourceSymbols then
                    if importsExact : source.symbols.imports =
                        bindings.importBindings.sourceImports then
                      have requestedException : plan.layout.requested.exceptionTable =
                          some exceptionTable := by
                        rw [prepareImage_requested prepared]
                        rfl
                      .ok ⟨unwind, source, (SourceResolve.resolve?_inputs resolved).1,
                        exceptionTable, rfl, provisionalFunction, tableBytes, rfl, plan, prepared,
                        requestedException, code, pdata, pdataSelected, pdataBytesExact,
                        xdata, xdataSelected, xdataBytesExact, bindings, staticsExact, importsExact⟩
                    else .error .finalImportsMismatch
                  else .error .finalStaticsMismatch
                else .error .xdataBytes
            else .error .pdataBytes

/-- `build?_eq_toOption` identifies this projection with diagnostic construction. -/
def build? {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    {table : StaticObjects.Table} (statics : StaticSection.Layout table)
    (sections : Sections) (requests : SourceImportRequests.Result splice) :
    Option (Result splice statics sections requests) :=
  (buildExcept splice statics sections requests).toOption

theorem build?_eq_toOption {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    {table : StaticObjects.Table} (statics : StaticSection.Layout table)
    (sections : Sections) (requests : SourceImportRequests.Result splice) :
    build? splice statics sections requests =
      (buildExcept splice statics sections requests).toOption := rfl

/-- The only runtime binding covers the entire final source code payload. -/
theorem Result.full_code_extent {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} {table : StaticObjects.Table}
    {statics : StaticSection.Layout table} {sections : Sections}
    {requests : SourceImportRequests.Result splice}
    (result : Result splice statics sections requests) :
    result.exceptionTable.functions =
      Vec.singleton (runtimeBinding result.source.bytes.length result.unwind) := by
  rw [result.exceptionExact]
  rfl

/-- Final `.pdata` length is obtained from the authoritative record serializer. -/
theorem Result.table_payload_length {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} {table : StaticObjects.Table}
    {statics : StaticSection.Layout table} {sections : Sections}
    {requests : SourceImportRequests.Result splice}
    (result : Result splice statics sections requests) :
    result.tableBytes.length = tableSize := by
  rw [result.tableBytesExact]
  simp [tableSize, placeholderTable]

/-- Final evidence comes from the production plan's validator, not from the
provisional runtime record used to calculate candidate table bytes. -/
theorem Result.final_exception_evidence {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} {table : StaticObjects.Table}
    {statics : StaticSection.Layout table} {sections : Sections}
    {requests : SourceImportRequests.Result splice}
    (result : Result splice statics sections requests) :
    Nonempty (ExceptionTableEvidence result.plan.layout.placed result.exceptionTable) :=
  result.plan.exceptionTable_evidence result.requestedException

/-- The metadata's prologue size selects the exact generated prologue from the
final source bytes. Section names remain supplied profile data. -/
theorem Result.unwind_source_prefix {frame rootOffset}
    {splice : SourceSplice.Result frame rootOffset} {table : StaticObjects.Table}
    {statics : StaticSection.Layout table} {sections : Sections}
    {requests : SourceImportRequests.Result splice}
    (result : Result splice statics sections requests) :
    result.source.bytes.toList.take result.unwind.info.layout.sizeOfProlog.toNat =
      ByteLayout.emitted splice.prologue.generated := by
  have prologueEq : result.source.splice.prologue = splice.prologue :=
    congrArg SourceSplice.Result.prologue result.sourceExact
  have bytesAppend := result.source.prologue_bytes_append
  rw [prologueEq] at bytesAppend
  rw [result.unwind.layout_exact]
  change result.source.bytes.toList.take
      (BitVec.toNat splice.prologue.unwindLayout.sizeOfProlog) = _
  rw [splice.prologue.stored_prologue_size, bytesAppend]
  simp

end Grass.Assembly.SourceLinkedImage
