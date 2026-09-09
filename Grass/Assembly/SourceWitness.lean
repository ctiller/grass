import Grass.Assembly.SourceLinkedImage
import Grass.Assembly.WriteAllGuardSource

/-!
# Authored source construction witness

Compose the existing checked source and PE producers while retaining every
caller-selected artifact input.  This is a construction witness only: it does
not identify a typed `MachineSource`, execute the image, or certify behavior.
-/

namespace Grass.Assembly.SourceWitness

open Grass.Artifact.PE

structure Inputs where
  table : StaticObjects.Table
  staticName : SectionName
  staticCharacteristics : BitVec 32
  libraryName : String
  sections : SourceLinkedImage.Sections

structure Result (authored : List Char) (inputs : Inputs) where
  body : SourceInput.Body
  bodyExact : (SourceInput.extractHelloSourceChars authored).toOption = some body
  frame : SourceFrame.Result
  frameExact : SourceFrame.derive? body = some frame
  splice : SourceSplice.Result frame 0
  spliceExact : SourceSplice.derive? frame 0 = some splice
  statics : StaticSection.Layout inputs.table
  staticsExact : StaticSection.layout? inputs.table inputs.staticName
    inputs.staticCharacteristics = some statics
  requests : SourceImportRequests.Result splice
  requestsExact : SourceImportRequests.resolve? splice inputs.libraryName = some requests
  linked : SourceLinkedImage.Result splice statics inputs.sections requests
  linkedExact : SourceLinkedImage.build? splice statics inputs.sections requests = some linked
  loop : WriteAllLoopSource.Selection linked.source
  loopExact : WriteAllLoopSource.select? linked.source = some loop
  guards : WriteAllGuardSource.AllSelection linked.source
  guardsExact : WriteAllGuardSource.selectAll? linked.source = some guards

/-- Run the authoritative checked producers and retain their exact success
equations in one dependent value. -/
def produce? (authored : List Char) (inputs : Inputs) : Option (Result authored inputs) :=
  match bodyExact : (SourceInput.extractHelloSourceChars authored).toOption with
  | none => none
  | some body =>
    match frameExact : SourceFrame.derive? body with
    | none => none
    | some frame =>
      match spliceExact : SourceSplice.derive? frame 0 with
      | none => none
      | some splice =>
        match staticsExact : StaticSection.layout? inputs.table inputs.staticName
            inputs.staticCharacteristics with
        | none => none
        | some statics =>
          match requestsExact : SourceImportRequests.resolve? splice inputs.libraryName with
          | none => none
          | some requests =>
            match linkedExact : SourceLinkedImage.build? splice statics inputs.sections requests with
            | none => none
            | some linked =>
              match loopExact : WriteAllLoopSource.select? linked.source with
              | none => none
              | some loop =>
                match guardsExact : WriteAllGuardSource.selectAll? linked.source with
                | none => none
                | some guards => some ⟨body, bodyExact, frame, frameExact, splice, spliceExact,
                    statics, staticsExact, requests, requestsExact, linked, linkedExact,
                    loop, loopExact, guards, guardsExact⟩

theorem eq_some_get {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value <;> simp_all

end Grass.Assembly.SourceWitness
