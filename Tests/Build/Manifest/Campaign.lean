import Grass.Build.Manifest.Campaign
import Tests.Build.Manifest.Comparison

/-! # Complete measured-campaign fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Manifest Grass.Specification Grass.Std.Logical

def allChanged (_ : ScopeId) : Bool := true

def scenarioChanges : ScenarioChanges
  | .cold => allChanged
  | .noOp => nothingChanged
  | .instructionBody => onlyAChanged
  | .localInvariant => onlyAChanged
  | .exportedInterface => interfaceChanged
  | .specificationKey => onlyAChanged
  | .layout => onlyAChanged
  | .providerProfile => interfaceChanged

def coldReport : BuildRunReport where
  scenario := .cold
  wallNanoseconds := 120
  peakResidentBytes := 800
  nodes := Vec.fromList
    [ reportNode leafA .coldBuild 1 11
    , reportNode leafB .coldBuild 2 7
    , reportNode component .coldBuild 3 13
    , reportNode product .coldBuild 4 17 ]

def leafEditReport (scenario : BuildScenario) : BuildRunReport :=
  { bodyEditReport with scenario := scenario }

def rebuiltFromImport : BuildDisposition :=
  .rebuilt (Vec.singleton .importedSummary) (by simp)

def interfaceEditReport (scenario : BuildScenario) : BuildRunReport where
  scenario := scenario
  wallNanoseconds := 55
  peakResidentBytes := 500
  nodes := Vec.fromList
    [ reportNode leafA .cacheHit 1 0
    , reportNode leafB .cacheHit 2 0
    , reportNode component rebuiltFromImport 3 13
    , reportNode product rebuiltFromImport 4 17 ]

def completeCampaign : MeasurementCampaign where
  runs := Vec.fromList
    [ coldReport
    , noOpReport
    , leafEditReport .instructionBody
    , leafEditReport .localInvariant
    , interfaceEditReport .exportedInterface
    , leafEditReport .specificationKey
    , leafEditReport .layout
    , interfaceEditReport .providerProfile ]

example : coldReport.ExactFor fixtureDag allChanged := by decide
example : (leafEditReport .localInvariant).ExactFor fixtureDag onlyAChanged := by decide
example : (interfaceEditReport .exportedInterface).ExactFor
    fixtureDag interfaceChanged := by decide

example : completeCampaign.Complete := by decide
example : completeCampaign.isComplete = true := by decide
example : completeCampaign.ExactFor fixtureDag scenarioChanges := by decide

example : (checkMeasurementCampaign fixtureDag scenarioChanges completeCampaign).isSome =
    true := by decide

/-- Removing the provider-profile sample makes coverage incomplete. -/
def incompleteCampaign : MeasurementCampaign where
  runs := completeCampaign.runs.take 7

example : ¬incompleteCampaign.Complete := by decide
example : incompleteCampaign.isComplete = false := by decide
example : checkMeasurementCampaign fixtureDag scenarioChanges incompleteCampaign = none :=
  by decide

/-- A complete label set with one dishonest cone is rejected by exact campaign
admission. -/
def overRebuildCampaign : MeasurementCampaign where
  runs := Vec.fromList
    [ coldReport
    , noOpReport
    , overRebuildReport
    , leafEditReport .localInvariant
    , interfaceEditReport .exportedInterface
    , leafEditReport .specificationKey
    , leafEditReport .layout
    , interfaceEditReport .providerProfile ]

example : overRebuildCampaign.Complete := by decide
example : ¬overRebuildCampaign.ExactFor fixtureDag scenarioChanges := by decide
example : checkMeasurementCampaign fixtureDag scenarioChanges overRebuildCampaign = none :=
  by decide

end Grass.Tests.Build.Manifest
