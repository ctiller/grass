import Grass.Build.Manifest.Evidence
import Tests.Build.Manifest.Campaign
import Tests.Build.Manifest.Rooted

/-! # Joint manifest-evidence admission fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Manifest Grass.Specification Grass.Std.Logical

example :
    (checkManifestEvidence fixtureDag scenarioChanges completeCampaign).isSome =
      true := by decide

example :
    checkManifestEvidence fixtureDag scenarioChanges incompleteCampaign = none :=
  by decide

example :
    checkManifestEvidence fixtureDag scenarioChanges overRebuildCampaign = none :=
  by decide

/-- A complete, cone-exact campaign cannot admit a cyclic manifest graph. -/
def cyclicNode : DependencyNode 1 where
  scope := leafA
  dependencies := Vec.singleton leafA
  bounded := by decide

def cyclicDag : ManifestDag 1 := ⟨Vec.singleton cyclicNode⟩

def noScenarioChanges (_ : ScopeId) : Bool := false

def emptyChanges : ScenarioChangePlan where
  cold := noScenarioChanges
  noOp := noScenarioChanges
  instructionBody := noScenarioChanges
  localInvariant := noScenarioChanges
  exportedInterface := noScenarioChanges
  specificationKey := noScenarioChanges
  layout := noScenarioChanges
  providerProfile := noScenarioChanges
  aggregateRebalance := noScenarioChanges
  processPrivateState := noScenarioChanges
  processLocalInvariant := noScenarioChanges
  processCancellationPoint := noScenarioChanges
  processExportedChannel := noScenarioChanges
  processSubsystemLowering := noScenarioChanges

def cyclicReport (scenario : BuildScenario) : BuildRunReport where
  scenario := scenario
  wallNanoseconds := 0
  peakResidentBytes := 0
  nodes := Vec.singleton (reportNode leafA .cacheHit 0 0)

def cyclicCampaign : MeasurementCampaign where
  runs := requiredBuildScenarios.map cyclicReport

example : cyclicCampaign.Complete := by decide
example : cyclicCampaign.ExactFor cyclicDag emptyChanges := by decide
example : ¬cyclicDag.WellFormed := by decide

example : checkManifestEvidence cyclicDag emptyChanges cyclicCampaign = none :=
  by decide

def disconnectedReport (scenario : BuildScenario) : BuildRunReport where
  scenario := scenario
  wallNanoseconds := 0
  peakResidentBytes := 0
  nodes := Vec.fromList
    [reportNode leafA .cacheHit 0 0, reportNode leafB .cacheHit 0 0]

def disconnectedCampaign : MeasurementCampaign where
  runs := requiredBuildScenarios.map disconnectedReport

example : disconnectedCampaign.Complete := by decide
example : disconnectedCampaign.ExactFor disconnectedDag emptyChanges := by decide
example : disconnectedDag.WellFormed := by decide
example : ¬disconnectedDag.Rooted := by decide

example :
    checkManifestEvidence disconnectedDag emptyChanges disconnectedCampaign = none :=
  by decide

example (evidence : CheckedManifestEvidence 4 scenarioChanges) :
    evidence.dag.graph.Rooted ∧
      evidence.campaign.campaign.Complete ∧
      evidence.campaign.campaign.ExactFor evidence.dag.graph scenarioChanges := by
  exact ⟨evidence.dag.rooted, evidence.campaignComplete,
    evidence.campaignExact⟩

end Grass.Tests.Build.Manifest
