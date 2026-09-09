import Grass.Assembly.SourceImage
import Grass.Assembly.SourceStaticBindings
import Grass.Assembly.SourceImportBindings
import Grass.Assembly.SourceImportRequests
import Grass.Artifact.PE.ImageWriter

/-! Two-pass code/static/import composition. `Result` binds final bytes and both
symbol populations to one checked PE plan and the exact input splice. This slice
does not yet attach required unwind metadata or establish loader, execution,
or specification correspondence; it is not an `emitProgram` acceptance path. -/

namespace Grass.Assembly.SourceLinkedImage
open Grass.Artifact.PE Grass.Std.Logical

structure Sections where
  codeName : SectionName
  codeCharacteristics : BitVec 32

def description {table : StaticObjects.Table} (sections : Sections)
    (statics : StaticSection.Layout table) (imports : Vec ImportLibrary)
    (code : Grass.Std.Logical.ByteArray) : ExecutableImageDescription :=
  { entryPoint := ⟨0, 0⟩
    sections := Vec.fromList [⟨sections.codeName, code, sections.codeCharacteristics⟩,
      statics.rawSection]
    imports }

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

def bindSymbols? (plan : ImagePlan) {table : StaticObjects.Table}
    (statics : StaticSection.Layout table) (libraryName : String) (names : List String) :
    Option (BoundSymbols plan statics libraryName names) := do
  let staticBindings ← SourceStaticBindings.resolve? plan statics 1
  match exact : SourceImportBindings.resolve? plan libraryName names with
  | none => none
  | some importBindings =>
    pure ⟨staticBindings, importBindings, (SourceImportBindings.resolve?_inputs exact).1,
      (SourceImportBindings.resolve?_inputs exact).2⟩

/-- Final code and symbols are checked against the actual final image, never only
against its provisional placement. -/
structure Result {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    {table : StaticObjects.Table} (statics : StaticSection.Layout table)
    (sections : Sections) (requests : SourceImportRequests.Result splice) where
  source : SourceResolve.Result frame rootOffset
  sourceExact : source.splice = splice
  plan : ImagePlan
  prepared : prepareImage (description sections statics (Vec.singleton requests.library) source.bytes) = .ok plan
  code : SourceImage.CodeSection source plan 0
  bindings : BoundSymbols plan statics requests.libraryName requests.sourceNames
  staticsExact : source.symbols.statics = bindings.staticBindings.sourceSymbols
  importsExact : source.symbols.imports = bindings.importBindings.sourceImports

/-- Derive provisional coordinates from instruction sizes, resolve source bytes,
then recompute and check every binding against the final prepared image. -/
def build? {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    {table : StaticObjects.Table} (statics : StaticSection.Layout table)
    (sections : Sections) (requests : SourceImportRequests.Result splice) :
    Option (Result splice statics sections requests) := do
  let imports := Vec.singleton requests.library
  let libraryName := requests.libraryName
  let names := requests.sourceNames
  let prototype ← (prepareImage (description sections statics imports
    (Vec.replicate splice.finalSizes.sum 0))).toOption
  let base ← prototype.resolveSectionBase? 0
  let preliminary ← bindSymbols? prototype statics libraryName names
  match resolved : SourceResolve.resolve? splice preliminary.symbols base.rva with
  | none => none
  | some source =>
    match prepared : prepareImage (description sections statics imports source.bytes) with
    | .error _ => none
    | .ok plan => do
      let code ← SourceImage.bindCode? source plan 0
      let bindings ← bindSymbols? plan statics libraryName names
      if staticsExact : source.symbols.statics = bindings.staticBindings.sourceSymbols then
        if importsExact : source.symbols.imports = bindings.importBindings.sourceImports then
          some ⟨source, (SourceResolve.resolve?_inputs resolved).1, plan, prepared,
            code, bindings, staticsExact, importsExact⟩
        else none
      else none

end Grass.Assembly.SourceLinkedImage
