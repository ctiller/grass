import Grass.Build.Manifest.Comparison

/-!
# Measured build campaigns

A campaign groups concrete run reports and checks coverage of every scenario
required by the sharding design. Repeated runs are allowed because measurement
needs samples, while coverage and exact rebuild-cone validation remain explicit.
-/

namespace Grass.Build.Manifest

open Grass.Specification Grass.Std.Logical

/-- Canonical scenario set required for a complete locality campaign. -/
def requiredBuildScenarios : Vec BuildScenario :=
  Vec.fromList
    [.cold, .noOp, .instructionBody, .localInvariant, .exportedInterface,
      .specificationKey, .layout, .providerProfile]

/-- A finite collection of measured build runs. -/
structure MeasurementCampaign where
  runs : Vec BuildRunReport

/-- Whether at least one run records the selected scenario. -/
def MeasurementCampaign.covers (campaign : MeasurementCampaign)
    (scenario : BuildScenario) : Bool :=
  campaign.runs.any fun report => decide (report.scenario = scenario)

/-- Every required scenario has at least one retained run. -/
def MeasurementCampaign.Complete (campaign : MeasurementCampaign) : Prop :=
  ∀ scenario ∈ requiredBuildScenarios,
    ∃ report ∈ campaign.runs, report.scenario = scenario

/-- Executable campaign coverage check. -/
def MeasurementCampaign.isComplete (campaign : MeasurementCampaign) : Bool :=
  requiredBuildScenarios.all campaign.covers

/-- `MeasurementCampaign.covers_eq_true_iff` connects the executable scenario
lookup to an exact retained witness. -/
theorem MeasurementCampaign.covers_eq_true_iff
    (campaign : MeasurementCampaign) (scenario : BuildScenario) :
    campaign.covers scenario = true ↔
      ∃ report ∈ campaign.runs, report.scenario = scenario := by
  simp [MeasurementCampaign.covers, Vec.any_eq_true_iff]

/-- `MeasurementCampaign.isComplete_eq_true_iff` proves that executable
campaign admission covers every and only scenario in `requiredBuildScenarios`. -/
theorem MeasurementCampaign.isComplete_eq_true_iff
    (campaign : MeasurementCampaign) :
    campaign.isComplete = true ↔ campaign.Complete := by
  simp [MeasurementCampaign.isComplete, MeasurementCampaign.Complete,
    Vec.all_eq_true_iff, MeasurementCampaign.covers_eq_true_iff]

/-- Scenario-indexed change predicates are supplied by the measurement harness,
not inferred from labels or timing data. -/
abbrev ScenarioChanges := BuildScenario → ScopeId → Bool

/-- Every retained run covers the same graph and reports exactly the rebuild
cone selected for its scenario by the harness plan. -/
def MeasurementCampaign.ExactFor {fanout : Nat}
    (campaign : MeasurementCampaign) (dag : ManifestDag fanout)
    (changes : ScenarioChanges) : Prop :=
  ∀ report ∈ campaign.runs,
    report.ExactFor dag (changes report.scenario)

instance MeasurementCampaign.instDecidableComplete
    (campaign : MeasurementCampaign) : Decidable campaign.Complete := by
  unfold Complete
  infer_instance

instance MeasurementCampaign.instDecidableExactFor {fanout : Nat}
    (campaign : MeasurementCampaign) (dag : ManifestDag fanout)
    (changes : ScenarioChanges) : Decidable (campaign.ExactFor dag changes) := by
  unfold ExactFor
  infer_instance

/-- Campaign metadata admitted only after coverage and exact cone checks. -/
structure CheckedMeasurementCampaign {fanout : Nat}
    (dag : ManifestDag fanout) (changes : ScenarioChanges) where
  campaign : MeasurementCampaign
  complete : campaign.Complete
  exact : campaign.ExactFor dag changes

/-- Validate generated campaign metadata against its graph and scenario plan. -/
def checkMeasurementCampaign {fanout : Nat} (dag : ManifestDag fanout)
    (changes : ScenarioChanges) (campaign : MeasurementCampaign) :
    Option (CheckedMeasurementCampaign dag changes) :=
  if complete : campaign.Complete then
    if exact : campaign.ExactFor dag changes then
      some ⟨campaign, complete, exact⟩
    else none
  else none

/-- `checkMeasurementCampaign_isSome_iff` states exact admission: both complete
scenario coverage and per-run rebuild-cone correspondence are necessary and
sufficient. -/
theorem checkMeasurementCampaign_isSome_iff {fanout : Nat}
    (dag : ManifestDag fanout) (changes : ScenarioChanges)
    (campaign : MeasurementCampaign) :
    (checkMeasurementCampaign dag changes campaign).isSome = true ↔
      campaign.Complete ∧ campaign.ExactFor dag changes := by
  by_cases complete : campaign.Complete
  · by_cases exact : campaign.ExactFor dag changes
    · simp [checkMeasurementCampaign, complete, exact]
    · simp [checkMeasurementCampaign, complete, exact]
  · simp [checkMeasurementCampaign, complete]

end Grass.Build.Manifest
