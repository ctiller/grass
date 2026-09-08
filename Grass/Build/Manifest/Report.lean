import Grass.Build.Manifest.Dag

/-!
# Caller-supplied build reports

Reports retain values attributed to one build scenario. This module does not
authenticate that a concrete process produced them and does not claim a
complexity bound. Elapsed time, peak resident memory, declaration counts, and
artifact sizes use explicit units and can be compared across records. An exact
record covers every manifest DAG node in traversal order, and its re-elaborated
scopes equal the independently computed rebuild cone.
-/

namespace Grass.Build.Manifest

open Grass.Build.Cache Grass.Specification Grass.Std.Logical

/-- The edit or build mode whose observed costs a report records. -/
inductive BuildScenario where
  | cold
  | noOp
  | instructionBody
  | localInvariant
  | exportedInterface
  | specificationKey
  | layout
  | providerProfile
  | aggregateRebalance
  | processPrivateState
  | processLocalInvariant
  | processCancellationPoint
  | processExportedChannel
  | processSubsystemLowering
  deriving DecidableEq, Repr

/-- Whether a disposition entails re-elaboration rather than exact replay. -/
def BuildDisposition.reElaborated : BuildDisposition → Bool
  | .coldBuild => true
  | .cacheHit => false
  | .rebuilt _ _ => true

/-- Per-node values attributed to one build run. The disposition determines
whether the node belongs to the reported re-elaboration cone. -/
structure NodeBuildReport where
  scope : ScopeId
  disposition : BuildDisposition
  kernelCheckedDeclarations : Nat
  measurement : BuildMeasurement

/-- One caller-supplied run report over a compact manifest graph. -/
structure BuildRunReport where
  scenario : BuildScenario
  wallNanoseconds : Nat
  peakResidentBytes : Nat
  nodes : Vec NodeBuildReport

/-- Exact retained input bytes for one scope before and after a scenario.
`none` is reserved for a scope absent before a cold build. Digest identities may
locate these bytes, but change detection below compares the bytes themselves. -/
structure ScopeInputTransition where
  scope : ScopeId
  before : Option (Vec UInt8)
  after : Vec UInt8
  deriving DecidableEq, Repr

/-- Whether the exact retained input for a scope changed. -/
def ScopeInputTransition.changed (input : ScopeInputTransition) : Bool :=
  decide (input.before ≠ some input.after)

/-- Where an observation envelope says its raw build record originated. This is
provenance metadata, not proof that the external process actually ran. -/
inductive ObservationSource where
  | localProcess
  | continuousIntegration (provider run : String)
  deriving DecidableEq, Repr

/-- Normative provenance retained beside one caller-supplied build report.
These fields make the empirical trust boundary auditable. Structural checking
does not authenticate them or turn their numeric payload into a theorem about a
physical process. -/
structure EvidenceEnvelope where
  schema : String
  schemaVersion : Nat
  gitTree : String
  profile : Option String
  leanVersion : String
  lakeVersion : String
  grassVersion : String
  normalizedCommand : String
  semanticEnvironment : Digest
  scenarioMutation : String
  beforeRoot : Digest
  afterRoot : Digest
  rawLog : Digest
  output : Digest
  reportDigest : Digest
  startedNanoseconds : Nat
  finishedNanoseconds : Nat
  source : ObservationSource
  deriving DecidableEq, Repr

/-- Minimal internal validity of provenance metadata. It rejects absent schema,
tree, tool, command, mutation, log, output, or payload identities and reversed
timestamps, but deliberately does not authenticate any identity. -/
def EvidenceEnvelope.StructurallyValid (envelope : EvidenceEnvelope) : Prop :=
  envelope.schema ≠ "" ∧ envelope.schemaVersion ≠ 0 ∧
    envelope.gitTree ≠ "" ∧ envelope.leanVersion ≠ "" ∧
    envelope.lakeVersion ≠ "" ∧ envelope.grassVersion ≠ "" ∧
    envelope.normalizedCommand ≠ "" ∧ envelope.scenarioMutation ≠ "" ∧
    envelope.rawLog.bytes.length ≠ 0 ∧ envelope.output.bytes.length ≠ 0 ∧
    envelope.reportDigest.bytes.length ≠ 0 ∧
    envelope.startedNanoseconds ≤ envelope.finishedNanoseconds

instance EvidenceEnvelope.instDecidableStructurallyValid
    (envelope : EvidenceEnvelope) : Decidable envelope.StructurallyValid := by
  unfold StructurallyValid
  infer_instance

/-- One untrusted observation record. `RetainedBuildRun.changed` derives the
change predicate used by structural checking from `inputs`; no predicate field
exists beside the report. -/
structure RetainedBuildRun where
  envelope : EvidenceEnvelope
  report : BuildRunReport
  inputs : Vec ScopeInputTransition
  manifestIdentities : Vec ManifestRecordIdentity

/-- Scopes visited by the build report, in manifest traversal order. -/
def BuildRunReport.visitedScopes (report : BuildRunReport) : Vec ScopeId :=
  report.nodes.map NodeBuildReport.scope

/-- Scopes whose disposition records cold or rebuilt work. -/
def BuildRunReport.reElaboratedScopes (report : BuildRunReport) : Vec ScopeId :=
  Vec.fromList <| report.nodes.toList.filterMap fun node =>
    if node.disposition.reElaborated then some node.scope else none

/-- Scope order retained by one observation record. -/
def RetainedBuildRun.inputScopes (run : RetainedBuildRun) : Vec ScopeId :=
  run.inputs.map ScopeInputTransition.scope

/-- Scope order of the exact manifest identities named by one report. -/
def RetainedBuildRun.manifestScopes (run : RetainedBuildRun) : Vec ScopeId :=
  run.manifestIdentities.map ManifestRecordIdentity.scope

/-- Change lookup derived from the retained exact input transition. Missing
scopes are not treated as changed; exact structural admission separately
requires the transition vector to match the DAG scope vector. -/
def RetainedBuildRun.changed (run : RetainedBuildRun) (scope : ScopeId) : Bool :=
  match run.inputs.toList.find? fun input => decide (input.scope = scope) with
  | none => false
  | some input => input.changed

/-- Scopes declared by a manifest DAG, in its child-before-parent order. -/
def ManifestDag.scopes {fanout : Nat} (dag : ManifestDag fanout) : Vec ScopeId :=
  dag.nodes.map DependencyNode.scope

/-- Exact structural correspondence between one report and its manifest graph. It
covers every graph node once in graph order and reports precisely the computed
rebuild cone as re-elaborated work. -/
def BuildRunReport.ExactFor {fanout : Nat} (report : BuildRunReport)
    (dag : ManifestDag fanout) (changed : ScopeId → Bool) : Prop :=
  report.visitedScopes = dag.scopes ∧
    report.reElaboratedScopes = rebuildCone dag changed

instance BuildRunReport.instDecidableExactFor {fanout : Nat}
    (report : BuildRunReport) (dag : ManifestDag fanout)
    (changed : ScopeId → Bool) : Decidable (report.ExactFor dag changed) := by
  unfold ExactFor
  infer_instance

/-- Structural consistency for an observation record. It connects the report
to every DAG scope and derives the rebuild cone from retained exact inputs. It
does not claim that the envelope or numeric measurements came from execution. -/
def RetainedBuildRun.StructurallyExactFor {fanout : Nat}
    (run : RetainedBuildRun) (dag : ManifestDag fanout) : Prop :=
  run.envelope.StructurallyValid ∧ run.inputScopes = dag.scopes ∧
    run.manifestScopes = dag.scopes ∧ run.report.ExactFor dag run.changed

instance RetainedBuildRun.instDecidableStructurallyExactFor {fanout : Nat}
    (run : RetainedBuildRun) (dag : ManifestDag fanout) :
    Decidable (run.StructurallyExactFor dag) := by
  unfold StructurallyExactFor
  infer_instance

/-- Aggregate node observations for one report. Byte counts and node durations
sum; node peak resident memory takes the maximum. These are deliberately named
differently from the run-level wall time and peak RSS retained by
`BuildRunReport`, because parallel job measurements are not additive. -/
structure BuildTotals where
  nodesVisited : Nat
  coldBuilds : Nat
  cacheHits : Nat
  rebuiltNodes : Nat
  reElaboratedNodes : Nat
  kernelCheckedDeclarations : Nat
  cumulativeNodeNanoseconds : Nat
  maxNodePeakResidentBytes : Nat
  oleanBytes : Nat
  proofBytes : Nat
  artifactBytes : Nat
  deriving DecidableEq, Repr

/-- Empty reported totals. -/
def BuildTotals.zero : BuildTotals where
  nodesVisited := 0
  coldBuilds := 0
  cacheHits := 0
  rebuiltNodes := 0
  reElaboratedNodes := 0
  kernelCheckedDeclarations := 0
  cumulativeNodeNanoseconds := 0
  maxNodePeakResidentBytes := 0
  oleanBytes := 0
  proofBytes := 0
  artifactBytes := 0

/-- Add one node's exact observations to running totals. -/
def BuildTotals.record (totals : BuildTotals) (node : NodeBuildReport) :
    BuildTotals :=
  let cold := match node.disposition with | .coldBuild => 1 | _ => 0
  let hit := match node.disposition with | .cacheHit => 1 | _ => 0
  let rebuilt := match node.disposition with | .rebuilt _ _ => 1 | _ => 0
  let reElaborated := if node.disposition.reElaborated then 1 else 0
  { nodesVisited := totals.nodesVisited + 1
    coldBuilds := totals.coldBuilds + cold
    cacheHits := totals.cacheHits + hit
    rebuiltNodes := totals.rebuiltNodes + rebuilt
    reElaboratedNodes := totals.reElaboratedNodes + reElaborated
    kernelCheckedDeclarations :=
      totals.kernelCheckedDeclarations + node.kernelCheckedDeclarations
    cumulativeNodeNanoseconds :=
      totals.cumulativeNodeNanoseconds + node.measurement.elapsedNanoseconds
    maxNodePeakResidentBytes :=
      max totals.maxNodePeakResidentBytes node.measurement.peakResidentBytes
    oleanBytes := totals.oleanBytes + node.measurement.oleanBytes
    proofBytes := totals.proofBytes + node.measurement.proofBytes
    artifactBytes := totals.artifactBytes + node.measurement.artifactBytes }

/-- Fold all node observations in manifest order. -/
def BuildRunReport.totals (report : BuildRunReport) : BuildTotals :=
  report.nodes.foldl BuildTotals.record BuildTotals.zero

/-- `BuildRunReport.totals_nodesVisited` proves that report aggregation counts
every recorded node exactly once. -/
theorem BuildRunReport.totals_nodesVisited (report : BuildRunReport) :
    report.totals.nodesVisited = report.nodes.length := by
  cases report with
  | mk scenario wall peak nodes =>
    change (nodes.foldl BuildTotals.record BuildTotals.zero).nodesVisited =
      nodes.length
    induction nodes using Vec.recOnPush with
    | empty => rfl
    | push nodes node inductionHypothesis =>
      simp [Vec.foldl_push, BuildTotals.record, inductionHypothesis]

/-- `BuildRunReport.totals_dispositions_partition` proves that cold builds,
cache hits, and rebuilt nodes partition every recorded node. -/
theorem BuildRunReport.totals_dispositions_partition (report : BuildRunReport) :
    report.totals.coldBuilds + report.totals.cacheHits +
      report.totals.rebuiltNodes = report.nodes.length := by
  cases report with
  | mk scenario wall peak nodes =>
    change (nodes.foldl BuildTotals.record BuildTotals.zero).coldBuilds +
      (nodes.foldl BuildTotals.record BuildTotals.zero).cacheHits +
      (nodes.foldl BuildTotals.record BuildTotals.zero).rebuiltNodes = nodes.length
    induction nodes using Vec.recOnPush with
    | empty => rfl
    | push nodes node inductionHypothesis =>
      rcases node with ⟨scope, disposition, declarations, measurement⟩
      cases disposition <;>
        simp [Vec.foldl_push, BuildTotals.record] <;> omega

/-- `BuildRunReport.totals_reElaboratedNodes` connects the derived work count
to the cold and rebuilt disposition counts. -/
theorem BuildRunReport.totals_reElaboratedNodes (report : BuildRunReport) :
    report.totals.reElaboratedNodes =
      report.totals.coldBuilds + report.totals.rebuiltNodes := by
  cases report with
  | mk scenario wall peak nodes =>
    change (nodes.foldl BuildTotals.record BuildTotals.zero).reElaboratedNodes =
      (nodes.foldl BuildTotals.record BuildTotals.zero).coldBuilds +
        (nodes.foldl BuildTotals.record BuildTotals.zero).rebuiltNodes
    induction nodes using Vec.recOnPush with
    | empty => rfl
    | push nodes node inductionHypothesis =>
      rcases node with ⟨scope, disposition, declarations, measurement⟩
      cases disposition <;>
        simp [Vec.foldl_push, BuildTotals.record,
          BuildDisposition.reElaborated] <;> omega

end Grass.Build.Manifest
