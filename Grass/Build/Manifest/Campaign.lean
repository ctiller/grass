import Grass.Build.Manifest.Comparison

/-!
# Structurally checked build campaigns

A campaign groups caller-supplied observation records and checks coverage of
every scenario required by the sharding design. Repeated runs are allowed, while
coverage and exact rebuild-cone validation remain explicit. This module checks
internal structure; it does not authenticate that a physical build occurred.
-/

namespace Grass.Build.Manifest

open Grass.Specification Grass.Std.Logical

/-- Canonical scenario set required for a complete locality campaign. -/
def requiredBuildScenarios : Vec BuildScenario :=
  Vec.fromList
    [.cold, .noOp, .instructionBody, .localInvariant, .exportedInterface,
      .specificationKey, .layout, .providerProfile, .aggregateRebalance,
      .processPrivateState, .processLocalInvariant, .processCancellationPoint,
      .processExportedChannel, .processSubsystemLowering]

/-- A finite collection of retained, caller-supplied build observations. The
name deliberately avoids claiming empirical authentication. -/
structure StructuralCampaign where
  runs : Vec RetainedBuildRun

/-- Whether at least one run records the selected scenario. -/
def StructuralCampaign.covers (campaign : StructuralCampaign)
    (scenario : BuildScenario) : Bool :=
  campaign.runs.any fun run => decide (run.report.scenario = scenario)

/-- Every required scenario has at least one retained run. -/
def StructuralCampaign.Complete (campaign : StructuralCampaign) : Prop :=
  ∀ scenario ∈ requiredBuildScenarios,
    ∃ run ∈ campaign.runs, run.report.scenario = scenario

/-- Executable campaign coverage check. -/
def StructuralCampaign.isComplete (campaign : StructuralCampaign) : Bool :=
  requiredBuildScenarios.all campaign.covers

/-- `StructuralCampaign.covers_eq_true_iff` connects the executable scenario
lookup to an exact retained witness. -/
theorem StructuralCampaign.covers_eq_true_iff
    (campaign : StructuralCampaign) (scenario : BuildScenario) :
    campaign.covers scenario = true ↔
      ∃ run ∈ campaign.runs, run.report.scenario = scenario := by
  simp [StructuralCampaign.covers, Vec.any_eq_true_iff]

/-- `StructuralCampaign.isComplete_eq_true_iff` proves that executable
campaign admission covers every and only scenario in `requiredBuildScenarios`. -/
theorem StructuralCampaign.isComplete_eq_true_iff
    (campaign : StructuralCampaign) :
    campaign.isComplete = true ↔ campaign.Complete := by
  simp [StructuralCampaign.isComplete, StructuralCampaign.Complete,
    Vec.all_eq_true_iff, StructuralCampaign.covers_eq_true_iff]

/-- An explicit change predicate for every normative locality scenario. The
named fields prevent a harness from silently omitting process-sharding or
aggregate-rebalance cases. -/
structure ScenarioChangePlan where
  cold : ScopeId → Bool
  noOp : ScopeId → Bool
  instructionBody : ScopeId → Bool
  localInvariant : ScopeId → Bool
  exportedInterface : ScopeId → Bool
  specificationKey : ScopeId → Bool
  layout : ScopeId → Bool
  providerProfile : ScopeId → Bool
  aggregateRebalance : ScopeId → Bool
  processPrivateState : ScopeId → Bool
  processLocalInvariant : ScopeId → Bool
  processCancellationPoint : ScopeId → Bool
  processExportedChannel : ScopeId → Bool
  processSubsystemLowering : ScopeId → Bool

/-- Select the exact named mutation predicate for one scenario. -/
def ScenarioChangePlan.forScenario (plan : ScenarioChangePlan) :
    BuildScenario → ScopeId → Bool
  | .cold => plan.cold
  | .noOp => plan.noOp
  | .instructionBody => plan.instructionBody
  | .localInvariant => plan.localInvariant
  | .exportedInterface => plan.exportedInterface
  | .specificationKey => plan.specificationKey
  | .layout => plan.layout
  | .providerProfile => plan.providerProfile
  | .aggregateRebalance => plan.aggregateRebalance
  | .processPrivateState => plan.processPrivateState
  | .processLocalInvariant => plan.processLocalInvariant
  | .processCancellationPoint => plan.processCancellationPoint
  | .processExportedChannel => plan.processExportedChannel
  | .processSubsystemLowering => plan.processSubsystemLowering

/-- Every retained run covers the same graph and reports exactly the rebuild
cone derived from that run's own exact before/after inputs. -/
def StructuralCampaign.ExactFor {fanout : Nat}
    (campaign : StructuralCampaign) (dag : ManifestDag fanout) : Prop :=
  ∀ run ∈ campaign.runs, run.StructurallyExactFor dag

instance StructuralCampaign.instDecidableComplete
    (campaign : StructuralCampaign) : Decidable campaign.Complete := by
  unfold Complete
  infer_instance

instance StructuralCampaign.instDecidableExactFor {fanout : Nat}
    (campaign : StructuralCampaign) (dag : ManifestDag fanout) :
    Decidable (campaign.ExactFor dag) := by
  unfold ExactFor
  infer_instance

/-- Caller-supplied campaign data admitted only after coverage and exact cone
checks. This is structural consistency, not empirical authentication. -/
structure CheckedStructuralCampaign {fanout : Nat}
    (dag : ManifestDag fanout) where
  campaign : StructuralCampaign
  complete : campaign.Complete
  exact : campaign.ExactFor dag

/-- Validate caller-supplied campaign structure against its graph. -/
def checkStructuralCampaign {fanout : Nat} (dag : ManifestDag fanout)
    (campaign : StructuralCampaign) : Option (CheckedStructuralCampaign dag) :=
  if complete : campaign.Complete then
    if exact : campaign.ExactFor dag then
      some ⟨campaign, complete, exact⟩
    else none
  else none

/-- `checkStructuralCampaign_isSome_iff` states exact admission: both complete
scenario coverage and per-run rebuild-cone correspondence are necessary and
sufficient. -/
theorem checkStructuralCampaign_isSome_iff {fanout : Nat}
    (dag : ManifestDag fanout) (campaign : StructuralCampaign) :
    (checkStructuralCampaign dag campaign).isSome = true ↔
      campaign.Complete ∧ campaign.ExactFor dag := by
  by_cases complete : campaign.Complete
  · by_cases exact : campaign.ExactFor dag
    · simp [checkStructuralCampaign, complete, exact]
    · simp [checkStructuralCampaign, complete, exact]
  · simp [checkStructuralCampaign, complete]

/-- Remove every report carrying one scenario label. -/
def StructuralCampaign.withoutScenario (campaign : StructuralCampaign)
    (scenario : BuildScenario) : StructuralCampaign where
  runs := Vec.fromList <| campaign.runs.toList.filter fun run =>
    decide (run.report.scenario ≠ scenario)

/-- Removing any required scenario makes campaign coverage incomplete,
independently of duplicate samples for other scenarios. -/
theorem StructuralCampaign.withoutScenario_not_complete
    (campaign : StructuralCampaign) (scenario : BuildScenario)
    (required : scenario ∈ requiredBuildScenarios) :
    ¬(campaign.withoutScenario scenario).Complete := by
  intro complete
  obtain ⟨run, present, same⟩ := complete scenario required
  have retained : run ∈ campaign.runs.toList ∧ run.report.scenario ≠ scenario := by
    simpa [StructuralCampaign.withoutScenario,
      Vec.mem_iff_mem_toList] using present
  exact retained.2 same

end Grass.Build.Manifest
