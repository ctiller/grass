import Grass.Build.Manifest.Campaign
import Grass.Build.Manifest.Rooted

/-!
# Joint manifest and structural-report admission

`CheckedManifestStructure` admits caller-supplied campaign data only together
with a structurally checked dependency DAG. It establishes internal graph and
cone consistency, not that an external build process produced the observations.
-/

namespace Grass.Build.Manifest

/-- A checked manifest DAG paired with a complete, structurally exact campaign. -/
structure CheckedManifestStructure (fanout : Nat) where
  dag : RootedManifestDag fanout
  campaign : CheckedStructuralCampaign dag.graph

/-- Jointly validate graph shape and caller-supplied campaign structure. -/
def checkManifestStructure {fanout : Nat} (dag : ManifestDag fanout)
    (campaign : StructuralCampaign) : Option (CheckedManifestStructure fanout) :=
  match checkRootedManifestDag dag with
  | none => none
  | some checkedDag =>
    match checkStructuralCampaign checkedDag.graph campaign with
    | none => none
    | some checkedCampaign => some ⟨checkedDag, checkedCampaign⟩

/-- `checkManifestStructure_isSome_iff` characterizes joint admission exactly. -/
theorem checkManifestStructure_isSome_iff {fanout : Nat}
    (dag : ManifestDag fanout) (campaign : StructuralCampaign) :
    (checkManifestStructure dag campaign).isSome = true ↔
      dag.Rooted ∧ campaign.Complete ∧ campaign.ExactFor dag := by
  by_cases rooted : dag.Rooted
  · by_cases complete : campaign.Complete
    · by_cases exact : campaign.ExactFor dag
      · simp [checkManifestStructure, checkRootedManifestDag,
          checkStructuralCampaign, rooted, complete, exact]
      · simp [checkManifestStructure, checkRootedManifestDag,
          checkStructuralCampaign, rooted, complete, exact]
    · simp [checkManifestStructure, checkRootedManifestDag,
        checkStructuralCampaign, rooted, complete]
  · simp [checkManifestStructure, checkRootedManifestDag, rooted]

/-- Successful joint admission exposes the checked graph ordering invariant. -/
theorem CheckedManifestStructure.dagWellFormed {fanout : Nat}
    (checked : CheckedManifestStructure fanout) :
    checked.dag.graph.WellFormed :=
  checked.dag.wellFormed

/-- Successful joint admission exposes complete scenario coverage. -/
theorem CheckedManifestStructure.campaignComplete {fanout : Nat}
    (checked : CheckedManifestStructure fanout) :
    checked.campaign.campaign.Complete :=
  checked.campaign.complete

/-- Successful joint admission exposes exact per-run rebuild cones. -/
theorem CheckedManifestStructure.campaignExact {fanout : Nat}
    (checked : CheckedManifestStructure fanout) :
    checked.campaign.campaign.ExactFor checked.dag.graph :=
  checked.campaign.exact

end Grass.Build.Manifest
