import Grass.Build.Manifest.Dag

/-!
# Measured build reports

Reports retain observations from one concrete build scenario. They do not claim
a complexity bound: elapsed time, peak resident memory, declaration counts, and
artifact sizes are recorded in explicit units and can be compared across runs.
An exact report covers every manifest DAG node in traversal order, and its
re-elaborated scopes equal the independently computed rebuild cone.
-/

namespace Grass.Build.Manifest

open Grass.Specification Grass.Std.Logical

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
  deriving DecidableEq, Repr

/-- Whether a disposition entails re-elaboration rather than exact replay. -/
def BuildDisposition.reElaborated : BuildDisposition → Bool
  | .coldBuild => true
  | .cacheHit => false
  | .rebuilt _ _ => true

/-- Per-node observations from one build run. The disposition determines
whether the node belongs to the measured re-elaboration cone. -/
structure NodeBuildReport where
  scope : ScopeId
  disposition : BuildDisposition
  kernelCheckedDeclarations : Nat
  measurement : BuildMeasurement

/-- One measured run over a compact manifest graph. -/
structure BuildRunReport where
  scenario : BuildScenario
  wallNanoseconds : Nat
  peakResidentBytes : Nat
  nodes : Vec NodeBuildReport

/-- Scopes visited by the build report, in manifest traversal order. -/
def BuildRunReport.visitedScopes (report : BuildRunReport) : Vec ScopeId :=
  report.nodes.map NodeBuildReport.scope

/-- Scopes whose disposition records cold or rebuilt work. -/
def BuildRunReport.reElaboratedScopes (report : BuildRunReport) : Vec ScopeId :=
  Vec.fromList <| report.nodes.toList.filterMap fun node =>
    if node.disposition.reElaborated then some node.scope else none

/-- Scopes declared by a manifest DAG, in its child-before-parent order. -/
def ManifestDag.scopes {fanout : Nat} (dag : ManifestDag fanout) : Vec ScopeId :=
  dag.nodes.map DependencyNode.scope

/-- Exact correspondence between one measured run and its manifest graph. It
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

/-- Empty measured totals. -/
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
