import Grass.Build.Manifest.Campaign
import Tests.Build.Manifest.Comparison

/-! # Complete structural-campaign fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Cache Grass.Build.Manifest Grass.Specification Grass.Std.Logical

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

def observationDigest : Digest := ⟨Vec.singleton 1⟩
def manifestDigest : Digest := ⟨Vec.empty⟩

def fixtureManifestEnvironment : SemanticEnvironment where
  source := manifestDigest
  importedSummaries := Vec.empty
  semanticProfile := manifestDigest
  verifier := manifestDigest
  toolchain := manifestDigest
  generator := manifestDigest
  options := manifestDigest
  auditPolicy := manifestDigest

def fixtureManifestMeasurement : BuildMeasurement where
  elapsedNanoseconds := 1
  peakResidentBytes := 2
  oleanBytes := 3
  proofBytes := 4
  artifactBytes := 5

def fixtureChildSummary (scope : ScopeId) : ChildSummary where
  scope := scope
  manifestRoot := manifestDigest
  publicSummary := manifestDigest

def fixtureLeafIdentity (scope : ScopeId) : ManifestRecordIdentity :=
  .leaf {
    identity := {
      scope := scope
      environment := fixtureManifestEnvironment
      cacheKey := manifestDigest
      manifestRoot := manifestDigest
      publicSummary := manifestDigest
      artifact := manifestDigest }
    measurement := fixtureManifestMeasurement
    disposition := .cacheHit }

def fixtureAggregateIdentity (scope : ScopeId) (children : Vec ChildSummary) :
    ManifestRecordIdentity :=
  .aggregate {
    identity := {
      scope := scope
      children := children
      manifestRoot := manifestDigest
      publicSummary := manifestDigest }
    measurement := fixtureManifestMeasurement }

def fixtureManifestIdentities : Vec ManifestRecordIdentity := Vec.fromList
  [ fixtureLeafIdentity leafA
  , fixtureLeafIdentity leafB
  , fixtureAggregateIdentity component
      (Vec.fromList [fixtureChildSummary leafA, fixtureChildSummary leafB])
  , fixtureAggregateIdentity product (Vec.singleton (fixtureChildSummary component)) ]

/-- Fixture provenance is deliberately only retained metadata. The structural
checker below does not claim that these fields authenticate an external run. -/
def fixtureEnvelope : EvidenceEnvelope where
  schema := "grass.build-run"
  schemaVersion := 1
  gitTree := "fixture-tree"
  profile := some "fixture-profile"
  leanVersion := "fixture-lean"
  lakeVersion := "fixture-lake"
  grassVersion := "fixture-grass"
  normalizedCommand := "lake build"
  semanticEnvironment := observationDigest
  scenarioMutation := "fixture-mutation"
  beforeRoot := observationDigest
  afterRoot := observationDigest
  rawLog := observationDigest
  output := observationDigest
  reportDigest := observationDigest
  startedNanoseconds := 1
  finishedNanoseconds := 2
  source := .localProcess

def inputTransition (changed : ScopeId → Bool) (scope : ScopeId) :
    ScopeInputTransition where
  scope := scope
  before := if changed scope then some (Vec.singleton 0) else some (Vec.singleton 1)
  after := Vec.singleton 1

def retainReport (report : BuildRunReport) : RetainedBuildRun where
  envelope := fixtureEnvelope
  report := report
  inputs := fixtureDag.scopes.map <| inputTransition
    (scenarioChanges.forScenario report.scenario)
  manifestIdentities := fixtureManifestIdentities

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

def completeCampaign : StructuralCampaign where
  runs := (Vec.fromList
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
    , interfaceEditReport .processSubsystemLowering ]).map retainReport

example : coldReport.ExactFor fixtureDag allChanged := by decide
example : (leafEditReport .localInvariant).ExactFor fixtureDag onlyAChanged := by decide
example : (interfaceEditReport .exportedInterface).ExactFor
    fixtureDag interfaceChanged := by decide

example : completeCampaign.Complete := by decide
example : completeCampaign.isComplete = true := by decide
example : completeCampaign.ExactFor fixtureDag := by decide
example : requiredBuildScenarios.length = 14 := by decide
example : completeCampaign.runs.length = 14 := by decide
example : completeCampaign.covers .aggregateRebalance = true := by decide
example : completeCampaign.covers .processPrivateState = true := by decide
example : completeCampaign.covers .processLocalInvariant = true := by decide
example : completeCampaign.covers .processCancellationPoint = true := by decide
example : completeCampaign.covers .processExportedChannel = true := by decide
example : completeCampaign.covers .processSubsystemLowering = true := by decide

example : (checkStructuralCampaign fixtureDag completeCampaign).isSome =
    true := by decide

/-- Removing the final process-subsystem-lowering sample makes coverage
incomplete. -/
def incompleteCampaign : StructuralCampaign where
  runs := completeCampaign.runs.take 13

example : ¬incompleteCampaign.Complete := by decide
example : incompleteCampaign.isComplete = false := by decide
example : checkStructuralCampaign fixtureDag incompleteCampaign = none :=
  by decide

/-- A complete label set with one dishonest cone is rejected by exact campaign
admission. -/
def overRebuildCampaign : StructuralCampaign where
  runs := (Vec.fromList
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
    , interfaceEditReport .processSubsystemLowering ]).map retainReport

example : overRebuildCampaign.Complete := by decide
example : ¬overRebuildCampaign.ExactFor fixtureDag := by decide
example : checkStructuralCampaign fixtureDag overRebuildCampaign = none :=
  by decide

example (scenario : BuildScenario) (required : scenario ∈ requiredBuildScenarios) :
    ¬(completeCampaign.withoutScenario scenario).Complete :=
  completeCampaign.withoutScenario_not_complete scenario required

end Grass.Tests.Build.Manifest
