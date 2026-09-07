import Grass.Build.Manifest.Report
import Tests.Build.Manifest.Dag

/-! # Measured build-report fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Manifest Grass.Specification Grass.Std.Logical

def reportMeasurement (scale : Nat) : BuildMeasurement where
  elapsedNanoseconds := 10 * scale
  peakResidentBytes := 100 * scale
  oleanBytes := 20 * scale
  proofBytes := 30 * scale
  artifactBytes := 40 * scale

def rebuiltFromSource : BuildDisposition :=
  .rebuilt (Vec.singleton .source) (by simp)

def reportNode (scope : ScopeId) (disposition : BuildDisposition)
    (scale declarations : Nat) : NodeBuildReport where
  scope := scope
  disposition := disposition
  kernelCheckedDeclarations := declarations
  measurement := reportMeasurement scale

/-- A body edit rebuilds one leaf and its two ancestors while replaying the
unchanged sibling. -/
def bodyEditReport : BuildRunReport where
  scenario := .instructionBody
  wallNanoseconds := 75
  peakResidentBytes := 650
  nodes := Vec.fromList
    [ reportNode leafA rebuiltFromSource 1 11
    , reportNode leafB .cacheHit 2 0
    , reportNode component rebuiltFromSource 3 13
    , reportNode product rebuiltFromSource 4 17 ]

example : bodyEditReport.ExactFor fixtureDag onlyAChanged := by
  decide

example : bodyEditReport.totals.nodesVisited = 4 := by decide
example : bodyEditReport.totals.cacheHits = 1 := by decide
example : bodyEditReport.totals.rebuiltNodes = 3 := by decide
example : bodyEditReport.totals.reElaboratedNodes = 3 := by decide
example : bodyEditReport.totals.kernelCheckedDeclarations = 41 := by decide
example : bodyEditReport.wallNanoseconds = 75 := by decide
example : bodyEditReport.peakResidentBytes = 650 := by decide
example : bodyEditReport.totals.cumulativeNodeNanoseconds = 100 := by decide
example : bodyEditReport.totals.maxNodePeakResidentBytes = 400 := by decide
example : bodyEditReport.totals.oleanBytes = 200 := by decide
example : bodyEditReport.totals.proofBytes = 300 := by decide
example : bodyEditReport.totals.artifactBytes = 400 := by decide

example : bodyEditReport.totals.nodesVisited = bodyEditReport.nodes.length :=
  bodyEditReport.totals_nodesVisited

example : bodyEditReport.totals.coldBuilds + bodyEditReport.totals.cacheHits +
    bodyEditReport.totals.rebuiltNodes = bodyEditReport.nodes.length :=
  bodyEditReport.totals_dispositions_partition

example : bodyEditReport.totals.reElaboratedNodes =
    bodyEditReport.totals.coldBuilds + bodyEditReport.totals.rebuiltNodes :=
  bodyEditReport.totals_reElaboratedNodes

/-- Marking the unchanged sibling as rebuilt contradicts the exact cone even
though all aggregate counts remain internally consistent. -/
def overRebuildReport : BuildRunReport where
  scenario := .instructionBody
  wallNanoseconds := 80
  peakResidentBytes := 700
  nodes := Vec.fromList
    [ reportNode leafA rebuiltFromSource 1 11
    , reportNode leafB rebuiltFromSource 2 7
    , reportNode component rebuiltFromSource 3 13
    , reportNode product rebuiltFromSource 4 17 ]

example : ¬overRebuildReport.ExactFor fixtureDag onlyAChanged := by decide

/-- Omitting a visited cache-hit node is rejected independently of the reported
re-elaboration cone. -/
def incompleteReport : BuildRunReport where
  scenario := .instructionBody
  wallNanoseconds := 70
  peakResidentBytes := 600
  nodes := Vec.fromList
    [ reportNode leafA rebuiltFromSource 1 11
    , reportNode component rebuiltFromSource 3 13
    , reportNode product rebuiltFromSource 4 17 ]

example : ¬incompleteReport.ExactFor fixtureDag onlyAChanged := by decide

end Grass.Tests.Build.Manifest
