import Grass.Build.Manifest.Evidence
import Tests.Build.Manifest.Campaign
import Tests.Build.Manifest.Rooted

/-! # Joint manifest-structure admission fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Manifest Grass.Specification Grass.Std.Logical

example :
    (checkManifestStructure fixtureDag completeCampaign).isSome =
      true := by decide

example :
    checkManifestStructure fixtureDag incompleteCampaign = none :=
  by decide

example :
    checkManifestStructure fixtureDag overRebuildCampaign = none :=
  by decide

def scrubMeasurement : BuildMeasurement where
  elapsedNanoseconds := 0
  peakResidentBytes := 0
  oleanBytes := 0
  proofBytes := 0
  artifactBytes := 0

def scrubNode (node : NodeBuildReport) : NodeBuildReport :=
  { node with kernelCheckedDeclarations := 0, measurement := scrubMeasurement }

def scrubReport (report : BuildRunReport) : BuildRunReport :=
  { report with
    wallNanoseconds := 0
    peakResidentBytes := 0
    nodes := report.nodes.map scrubNode }

def scrubRun (run : RetainedBuildRun) : RetainedBuildRun :=
  { run with report := scrubReport run.report }

/-- Fabricated zero counters remain internally cone-consistent, so they inhabit
only the honestly named structural campaign. There is intentionally no checked
"measured evidence" type or theorem claiming these values came from execution. -/
def fabricatedZeroCampaign : StructuralCampaign where
  runs := completeCampaign.runs.map scrubRun

example : fabricatedZeroCampaign.Complete := by decide
example : fabricatedZeroCampaign.ExactFor fixtureDag := by decide
example : (checkManifestStructure fixtureDag fabricatedZeroCampaign).isSome = true :=
  by decide

def missingRawLogEnvelope : EvidenceEnvelope :=
  { fixtureEnvelope with rawLog := ⟨Vec.empty⟩ }

def missingRawLogCampaign : StructuralCampaign where
  runs := completeCampaign.runs.map fun run =>
    { run with envelope := missingRawLogEnvelope }

/-- Even structural admission requires every normative provenance identity. -/
example : ¬missingRawLogCampaign.ExactFor fixtureDag := by decide
example : checkManifestStructure fixtureDag missingRawLogCampaign = none := by decide

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

def retainCyclicReport (report : BuildRunReport) : RetainedBuildRun where
  envelope := fixtureEnvelope
  report := report
  inputs := cyclicDag.scopes.map (inputTransition noScenarioChanges)

def cyclicCampaign : StructuralCampaign where
  runs := (requiredBuildScenarios.map cyclicReport).map retainCyclicReport

example : cyclicCampaign.Complete := by decide
example : cyclicCampaign.ExactFor cyclicDag := by decide
example : ¬cyclicDag.WellFormed := by decide

example : checkManifestStructure cyclicDag cyclicCampaign = none :=
  by decide

def disconnectedReport (scenario : BuildScenario) : BuildRunReport where
  scenario := scenario
  wallNanoseconds := 0
  peakResidentBytes := 0
  nodes := Vec.fromList
    [reportNode leafA .cacheHit 0 0, reportNode leafB .cacheHit 0 0]

def retainDisconnectedReport (report : BuildRunReport) : RetainedBuildRun where
  envelope := fixtureEnvelope
  report := report
  inputs := disconnectedDag.scopes.map (inputTransition noScenarioChanges)

def disconnectedCampaign : StructuralCampaign where
  runs := (requiredBuildScenarios.map disconnectedReport).map
    retainDisconnectedReport

example : disconnectedCampaign.Complete := by decide
example : disconnectedCampaign.ExactFor disconnectedDag := by decide
example : disconnectedDag.WellFormed := by decide
example : ¬disconnectedDag.Rooted := by decide

example :
    checkManifestStructure disconnectedDag disconnectedCampaign = none :=
  by decide

example (checked : CheckedManifestStructure 4) :
    checked.dag.graph.Rooted ∧
      checked.campaign.campaign.Complete ∧
      checked.campaign.campaign.ExactFor checked.dag.graph := by
  exact ⟨checked.dag.rooted, checked.campaignComplete,
    checked.campaignExact⟩

end Grass.Tests.Build.Manifest
