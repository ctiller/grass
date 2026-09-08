import Grass.Build.Manifest.Campaign
import Grass.Build.Manifest.Rooted

/-!
# Joint DAG and structural-report admission

`CheckedDagCampaignStructure` admits caller-supplied campaign data only together
with a structurally checked dependency DAG. Concrete manifest identity is
checked separately by `checkHierarchyStructure`; this module establishes only
graph and cone consistency.
-/

namespace Grass.Build.Manifest

/-- A checked manifest DAG paired with a complete, structurally exact campaign. -/
structure CheckedDagCampaignStructure (fanout : Nat) where
  dag : RootedManifestDag fanout
  campaign : CheckedStructuralCampaign dag.graph

/-- Jointly validate graph shape and caller-supplied campaign structure. -/
def checkDagCampaignStructure {fanout : Nat} (dag : ManifestDag fanout)
    (campaign : StructuralCampaign) : Option (CheckedDagCampaignStructure fanout) :=
  match checkRootedManifestDag dag with
  | none => none
  | some checkedDag =>
    match checkStructuralCampaign checkedDag.graph campaign with
    | none => none
    | some checkedCampaign => some ⟨checkedDag, checkedCampaign⟩

/-- `checkDagCampaignStructure_isSome_iff` characterizes joint admission exactly. -/
theorem checkDagCampaignStructure_isSome_iff {fanout : Nat}
    (dag : ManifestDag fanout) (campaign : StructuralCampaign) :
    (checkDagCampaignStructure dag campaign).isSome = true ↔
      dag.Rooted ∧ campaign.Complete ∧ campaign.ExactFor dag := by
  by_cases rooted : dag.Rooted
  · by_cases complete : campaign.Complete
    · by_cases exact : campaign.ExactFor dag
      · simp [checkDagCampaignStructure, checkRootedManifestDag,
          checkStructuralCampaign, rooted, complete, exact]
      · simp [checkDagCampaignStructure, checkRootedManifestDag,
          checkStructuralCampaign, rooted, complete, exact]
    · simp [checkDagCampaignStructure, checkRootedManifestDag,
        checkStructuralCampaign, rooted, complete]
  · simp [checkDagCampaignStructure, checkRootedManifestDag, rooted]

/-- Successful joint admission exposes the checked graph ordering invariant. -/
theorem CheckedDagCampaignStructure.dagWellFormed {fanout : Nat}
    (checked : CheckedDagCampaignStructure fanout) :
    checked.dag.graph.WellFormed :=
  checked.dag.wellFormed

/-- Successful joint admission exposes complete scenario coverage. -/
theorem CheckedDagCampaignStructure.campaignComplete {fanout : Nat}
    (checked : CheckedDagCampaignStructure fanout) :
    checked.campaign.campaign.Complete :=
  checked.campaign.complete

/-- Successful joint admission exposes exact per-run rebuild cones. -/
theorem CheckedDagCampaignStructure.campaignExact {fanout : Nat}
    (checked : CheckedDagCampaignStructure fanout) :
    checked.campaign.campaign.ExactFor checked.dag.graph :=
  checked.campaign.exact

end Grass.Build.Manifest
