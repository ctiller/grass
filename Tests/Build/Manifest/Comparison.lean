import Grass.Build.Manifest.Comparison
import Tests.Build.Manifest.Report

/-! # Exact measured build-comparison fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Manifest Grass.Std.Logical

def noOpReport : BuildRunReport where
  scenario := .noOp
  wallNanoseconds := 10
  peakResidentBytes := 100
  nodes := Vec.fromList
    [ reportNode leafA .cacheHit 0 0
    , reportNode leafB .cacheHit 0 0
    , reportNode component .cacheHit 0 0
    , reportNode product .cacheHit 0 0 ]

example : noOpReport.ExactFor fixtureDag nothingChanged := by decide

def noOpToBodyEdit : BuildRunComparison :=
  compareBuildRuns noOpReport bodyEditReport

example : noOpToBodyEdit.ExactFor noOpReport bodyEditReport :=
  compareBuildRuns_exact noOpReport bodyEditReport

example : noOpToBodyEdit.previousScenario = .noOp := rfl
example : noOpToBodyEdit.currentScenario = .instructionBody := rfl
example : noOpToBodyEdit.wallNanoseconds = .increased 65 := by decide
example : noOpToBodyEdit.peakResidentBytes = .increased 550 := by decide
example : noOpToBodyEdit.reElaboratedNodes = .increased 3 := by decide
example : noOpToBodyEdit.kernelCheckedDeclarations = .increased 41 := by decide
example : noOpToBodyEdit.oleanBytes = .increased 200 := by decide
example : noOpToBodyEdit.proofBytes = .increased 300 := by decide
example : noOpToBodyEdit.artifactBytes = .increased 400 := by decide

example : compareNat 75 10 = .decreased 65 := by decide
example : compareNat 75 75 = .unchanged := by decide

/-- Reversing only the claimed wall-time direction is rejected by the exact
arithmetic specification. -/
def dishonestComparison : BuildRunComparison :=
  { noOpToBodyEdit with wallNanoseconds := .decreased 65 }

example : ¬dishonestComparison.ExactFor noOpReport bodyEditReport := by decide

end Grass.Tests.Build.Manifest
