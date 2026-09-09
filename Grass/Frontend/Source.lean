import Grass.Frontend.Target
import Grass.Assembly.SourceLinkedImage

namespace Grass

namespace Frontend
open Assembly Artifact.PE

/-- Constructor-selected layout conventions, not additional source arguments. -/
structure Layout where
  staticName : SectionName
  staticCharacteristics : BitVec 32
  libraryName : String
  sections : SourceLinkedImage.Sections

def win10Layout : Layout where
  staticName := ⟨Std.Logical.Text.utf8 ".rdata", by decide⟩
  staticCharacteristics := 0x40000040
  libraryName := "kernel32.dll"
  sections := {
    codeName := ⟨Std.Logical.Text.utf8 ".text", by decide⟩
    codeCharacteristics := 0x60000020
    pdataName := ⟨Std.Logical.Text.utf8 ".pdata", by decide⟩
    xdataName := ⟨Std.Logical.Text.utf8 ".xdata", by decide⟩ }

end Frontend

def PlatformPlan.layout {requirements : Specification.RequirementSet}
    (_plan : PlatformPlan requirements) : Frontend.Layout := Frontend.win10Layout

namespace Frontend
open Assembly

/-- Structural construction evidence for the supplied ingress and actual table.
Loop invariants, execution and specification correspondence are separate. -/
structure Construction (body : SourceInput.Body) (table : StaticObjects.Table) (layout : Layout) where
  frame : SourceFrame.Result
  frameExact : SourceFrame.derive? body = some frame
  splice : SourceSplice.Result frame 0
  spliceExact : SourceSplice.derive? frame 0 = some splice
  statics : StaticSection.Layout table
  staticsExact : StaticSection.layout? table layout.staticName layout.staticCharacteristics = some statics
  requests : SourceImportRequests.Result splice
  requestsExact : SourceImportRequests.resolve? splice layout.libraryName = some requests
  linked : SourceLinkedImage.Result splice statics layout.sections requests
  linkedExact : SourceLinkedImage.build? splice statics layout.sections requests = some linked

def construct? (body : SourceInput.Body) (table : StaticObjects.Table) (layout : Layout) :
    Option (Construction body table layout) :=
  match frameExact : SourceFrame.derive? body with
  | none => none
  | some frame =>
    match spliceExact : SourceSplice.derive? frame 0 with
    | none => none
    | some splice =>
      match staticsExact : StaticSection.layout? table layout.staticName layout.staticCharacteristics with
      | none => none
      | some statics =>
        match requestsExact : SourceImportRequests.resolve? splice layout.libraryName with
        | none => none
        | some requests =>
          match linkedExact : SourceLinkedImage.build? splice statics layout.sections requests with
          | none => none
          | some linked => some ⟨frame, frameExact, splice, spliceExact, statics, staticsExact,
              requests, requestsExact, linked, linkedExact⟩

end Frontend

/-- The initial ingress is the exact supported Hello declaration. Additional
ingresses require their own checked connection, not an unrelated parsed body. -/
inductive SourceIngress (authored : List Char) (body : Assembly.SourceInput.Body) : Prop where
  | hello (extracted :
      (Assembly.SourceInput.extractHelloSourceChars authored).toOption = some body)

/-- A source is indexed by the entire selected plan, including its exact root.
The current ingress parser is explicitly Hello-specific, while construction
evidence contains no Hello loop/guard or execution certificate. -/
structure MachineSource {requirements : Specification.RequirementSet}
    (plan : PlatformPlan requirements) where
  authored : List Char
  table : Assembly.StaticObjects.Table
  body : Assembly.SourceInput.Body
  ingress : SourceIngress authored body
  construction : Frontend.Construction body table plan.layout

namespace MachineSource
variable {requirements : Specification.RequirementSet}

/-- Run checked producers on the actual declaration characters and table value. -/
def ofHello? (plan : PlatformPlan requirements) (authored : List Char)
    (table : Assembly.StaticObjects.Table) : Option (MachineSource plan) :=
  match bodyExact : (Assembly.SourceInput.extractHelloSourceChars authored).toOption with
  | none => none
  | some body =>
    match Frontend.construct? body table plan.layout with
    | none => none
    | some construction => some ⟨authored, table, body, .hello bodyExact, construction⟩

theorem ofHello?_inputs {plan : PlatformPlan requirements} {authored : List Char}
    {table : Assembly.StaticObjects.Table} {source : MachineSource plan}
    (produced : ofHello? plan authored table = some source) :
    source.authored = authored ∧ source.table = table := by
  unfold ofHello? at produced
  split at produced
  · contradiction
  · split at produced
    · contradiction
    · cases produced
      exact ⟨rfl, rfl⟩

end MachineSource
end Grass
