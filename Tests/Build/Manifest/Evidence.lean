import Grass.Build.Manifest.Evidence
import Tests.Build.Manifest.Campaign

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

def emptyChanges (_ : BuildScenario) (_ : ScopeId) : Bool := false

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

example (evidence : CheckedManifestEvidence 4 scenarioChanges) :
    evidence.dag.graph.WellFormed ∧
      evidence.campaign.campaign.Complete ∧
      evidence.campaign.campaign.ExactFor evidence.dag.graph scenarioChanges := by
  exact ⟨evidence.dagWellFormed, evidence.campaignComplete,
    evidence.campaignExact⟩

end Grass.Tests.Build.Manifest
