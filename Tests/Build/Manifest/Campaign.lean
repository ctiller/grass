import Grass.Build.Manifest.Campaign
import Tests.Build.Manifest.Comparison

/-! # Complete measured-campaign fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Manifest Grass.Specification Grass.Std.Logical

def allChanged (_ : ScopeId) : Bool := true

def scenarioChanges : ScenarioChangePlan where
  cold := allChanged
  noOp := nothingChanged
  instructionBody := onlyAChanged
  localInvariant := onlyAChanged
  exportedInterface := interfaceChanged
  specificationKey := onlyAChanged
  layout := onlyAChanged
  providerProfile := interfaceChanged
  aggregateRebalance := interfaceChanged
  processPrivateState := onlyAChanged
  processLocalInvariant := onlyAChanged
  processCancellationPoint := onlyAChanged
  processExportedChannel := interfaceChanged
  processSubsystemLowering := interfaceChanged

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
    , interfaceEditReport .providerProfile
    , interfaceEditReport .aggregateRebalance
    , leafEditReport .processPrivateState
    , leafEditReport .processLocalInvariant
    , leafEditReport .processCancellationPoint
    , interfaceEditReport .processExportedChannel
    , interfaceEditReport .processSubsystemLowering ]

example : coldReport.ExactFor fixtureDag allChanged := by decide
example : (leafEditReport .localInvariant).ExactFor fixtureDag onlyAChanged := by decide
example : (interfaceEditReport .exportedInterface).ExactFor
    fixtureDag interfaceChanged := by decide

example : completeCampaign.Complete := by decide
example : completeCampaign.isComplete = true := by decide
example : completeCampaign.ExactFor fixtureDag scenarioChanges := by decide
example : requiredBuildScenarios.length = 14 := by decide
example : completeCampaign.runs.length = 14 := by decide
example : completeCampaign.covers .aggregateRebalance = true := by decide
example : completeCampaign.covers .processPrivateState = true := by decide
example : completeCampaign.covers .processLocalInvariant = true := by decide
example : completeCampaign.covers .processCancellationPoint = true := by decide
example : completeCampaign.covers .processExportedChannel = true := by decide
example : completeCampaign.covers .processSubsystemLowering = true := by decide

example : (checkMeasurementCampaign fixtureDag scenarioChanges completeCampaign).isSome =
    true := by decide

/-- Removing the final process-subsystem-lowering sample makes coverage
incomplete. -/
def incompleteCampaign : MeasurementCampaign where
  runs := completeCampaign.runs.take 13

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
    , interfaceEditReport .providerProfile
    , interfaceEditReport .aggregateRebalance
    , leafEditReport .processPrivateState
    , leafEditReport .processLocalInvariant
    , leafEditReport .processCancellationPoint
    , interfaceEditReport .processExportedChannel
    , interfaceEditReport .processSubsystemLowering ]

example : overRebuildCampaign.Complete := by decide
example : ¬overRebuildCampaign.ExactFor fixtureDag scenarioChanges := by decide
example : checkMeasurementCampaign fixtureDag scenarioChanges overRebuildCampaign = none :=
  by decide

example (scenario : BuildScenario) (required : scenario ∈ requiredBuildScenarios) :
    ¬(completeCampaign.withoutScenario scenario).Complete :=
  completeCampaign.withoutScenario_not_complete scenario required

end Grass.Tests.Build.Manifest
