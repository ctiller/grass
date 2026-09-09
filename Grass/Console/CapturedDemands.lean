import Grass.Console.Captured
import Grass.Console.Timing
import Grass.Core.Demand
import Std.Data.String.ToNat

/-!
# Demands of the exact captured console context

Keys 0, 1 and 2 select finite byte accounting, unrestricted waiting coverage and
the selected resource snapshot. Each appended liveness fragment owns a further
key. `demandIdentity_injective` checks the generated decimal identities; append
preserves the positions of existing demands. These are author-side demands of
the intermediate console context, not lowering certificates or the legacy root.
-/

namespace Grass.Console

open Resource Semantics RelationalSystem

/-- Dependency vocabulary for this console consumer, not a universal facet registry. -/
inductive CapturedFacet where
  | logicalText
  | representation
  | responseLaw
  | resourceSelection
  | boundaryTiming
deriving DecidableEq

namespace CapturedContext

variable {R Outcome : Type} [ResourceModel R] {resources : R}

/-- The output demand ranges over every initialized finite history of every
selected rendering, rather than only success observations. -/
def OutputExact (context : CapturedContext resources Outcome) : Prop :=
  ∀ rendering (history : (context.request.system rendering).History),
    Behavior.emittedBytes history.path.events = Accounting.committed history.state

/-- The unrestricted domain retains a permanent wait at every represented cut. -/
def WaitsComplete (context : CapturedContext resources Outcome) : Prop :=
  ∀ (rendering : Specification.LineRendering) (cut : OutputCut (rendering.bytes context.request.line)),
    Nonempty (PermanentWait (Behavior.boundary (rendering.bytes context.request.line))
      (Behavior.pendingAt _ cut))

/-- The selected capability snapshot has the declared empty console axis set. -/
def ResourcesExact (context : CapturedContext resources Outcome) : Prop :=
  context.resourceSemantics.selectedAxes = []

/-- The isolated timing premise is inhabited with exact terminal extensions;
termination ranges independently over every generated maximal behavior. -/
def BoundaryTermination (context : CapturedContext resources Outcome) : Prop :=
  ∀ rendering : Specification.LineRendering,
    let boundary := Behavior.boundary (rendering.bytes context.request.line)
    BoundaryTerminalAdequate boundary ∧
    BoundaryResponsive (BoundaryTimingStrategy.responding boundary) ∧
    Nonempty (BoundaryTimingStrategy.responding boundary).GeneratedComplete ∧
    ∀ strategy : BoundaryTimingStrategy boundary, BoundaryResponsive strategy →
      ∀ complete : strategy.GeneratedComplete,
        ∃ history finished, complete.1 = CompleteHistory.terminal history finished

def livenessStatement (context : CapturedContext resources Outcome) : CapturedLiveness → Prop
  | .terminatesUnderBoundaryResponse => context.BoundaryTermination

theorem outputExact (context : CapturedContext resources Outcome) : context.OutputExact :=
  fun _ history => Accounting.history_accounting history

theorem waitsComplete (context : CapturedContext resources Outcome) : context.WaitsComplete :=
  fun rendering cut => ⟨Behavior.permanentWaitAt (rendering.bytes context.request.line) cut⟩

theorem resourcesExact (context : CapturedContext resources Outcome) : context.ResourcesExact :=
  context.resourceSemantics.selectedAxes_empty

theorem boundaryTermination (context : CapturedContext resources Outcome) :
    context.BoundaryTermination := by
  intro rendering
  refine ⟨Timing.completionAdequate _, Timing.respondingResponsive _,
    Timing.respondingGeneratedNonempty (Behavior.initial _), ?_⟩
  exact fun strategy responsive complete => Timing.generated_terminates strategy responsive complete

theorem livenessCorrect (context : CapturedContext resources Outcome)
    (fragment : CapturedLiveness) : context.livenessStatement fragment := by
  cases fragment
  exact context.boundaryTermination

end CapturedContext

namespace CapturedSpecification

variable {R Outcome : Type} [ResourceModel R] {resources : R}

/-- Deterministic positional keys stay stable when fragments are appended. -/
def demandIdentity (position : Nat) : RequirementKey :=
  ⟨⟨"Grass.Console.CapturedSpecification", Nat.repr position⟩⟩

theorem demandIdentity_injective : Function.Injective demandIdentity := by
  intro first second equal
  exact Nat.repr_injective (congrArg (fun key => key.id.localName) equal)

abbrev DemandKey (spec : CapturedSpecification resources Outcome) :=
  Fin (3 + spec.suite.liveness.length)

def demandStatement (spec : CapturedSpecification resources Outcome) (key : spec.DemandKey) : Prop :=
  if zero : key.val = 0 then spec.context.OutputExact
  else if one : key.val = 1 then spec.context.WaitsComplete
  else if two : key.val = 2 then spec.context.ResourcesExact
  else spec.context.livenessStatement (spec.suite.liveness[key.val - 3]'(by
    have bound := key.isLt
    omega))

def demandKind (spec : CapturedSpecification resources Outcome) (key : spec.DemandKey) : RequirementKind :=
  if key.val = 0 then .functional
  else if key.val = 1 then .progress
  else if key.val = 2 then .resource
  else .termination

/-- Dependencies select the semantic parts actually consumed by each demand. -/
def dependencies (spec : CapturedSpecification resources Outcome)
    (key : spec.DemandKey) : List CapturedFacet :=
  if key.val = 0 then [.logicalText, .representation, .responseLaw]
  else if key.val = 1 then [.logicalText, .representation, .responseLaw]
  else if key.val = 2 then [.resourceSelection]
  else [.logicalText, .representation, .responseLaw, .boundaryTiming]

/-- The existing keyed-demand infrastructure receives statements computed from
this exact context and fragment list, with no independently replaceable family. -/
def demands (spec : CapturedSpecification resources Outcome) : DemandFamily where
  Key := spec.DemandKey
  keys := List.finRange _
  complete := fun _ => List.mem_finRange _
  unique := List.nodup_finRange _
  identity := fun key => demandIdentity key.val
  identityInjective := fun _ _ equal => Fin.ext (demandIdentity_injective equal)
  kind := spec.demandKind
  statement := spec.demandStatement

/-- The author-side proof covers each independently keyed computed demand. -/
theorem meetsDemands (spec : CapturedSpecification resources Outcome) :
    DemandCertificateFamily spec.demands := by
  constructor
  intro key
  change spec.demandStatement key
  unfold demandStatement
  split
  · exact spec.context.outputExact
  · split
    · exact spec.context.waitsComplete
    · split
      · exact spec.context.resourcesExact
      · exact spec.context.livenessCorrect _

/-- Appending gives the new fragment its own additional demand. -/
theorem withLiveness_demandCount (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) :
    (spec.withLiveness fragment).demands.keys.length = spec.demands.keys.length + 1 := by
  simp [demands, withLiveness, List.length_finRange, Nat.add_assoc]

/-- An existing demand keeps its position in the appended family. -/
def oldKey (spec : CapturedSpecification resources Outcome) (fragment : CapturedLiveness)
    (key : spec.DemandKey) : (spec.withLiveness fragment).DemandKey :=
  ⟨key.val, by
    have bound := key.isLt
    change key.val < 3 + (spec.suite.liveness ++ [fragment]).length
    simp only [List.length_append, List.length_singleton]
    omega⟩

theorem withLiveness_oldIdentity (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) (key : spec.DemandKey) :
    (spec.withLiveness fragment).demands.identity (spec.oldKey fragment key) =
      spec.demands.identity key := rfl

theorem withLiveness_oldDependencies (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) (key : spec.DemandKey) :
    (spec.withLiveness fragment).dependencies (spec.oldKey fragment key) =
      spec.dependencies key := rfl

/-- `withLiveness_oldStatement` preserves each prior proposition; the preceding
identity and dependency laws cover its stable key and metadata. -/
theorem withLiveness_oldStatement (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) (key : spec.DemandKey) :
    (spec.withLiveness fragment).demands.statement (spec.oldKey fragment key) =
      spec.demands.statement key := by
  change (spec.withLiveness fragment).demandStatement (spec.oldKey fragment key) =
    spec.demandStatement key
  unfold demandStatement
  simp only [oldKey, withLiveness_context]
  by_cases zero : key.val = 0
  · simp [zero]
  by_cases one : key.val = 1
  · simp [one]
  by_cases two : key.val = 2
  · simp [two]
  have bounded : key.val - 3 < spec.suite.liveness.length := by
    have bound := key.isLt
    omega
  simp [zero, one, two, withLiveness, List.getElem_append_left bounded]

end CapturedSpecification
end Grass.Console
