import Grass.Build.Manifest.Campaign

/-!
# Joint manifest and measurement admission

`CheckedManifestEvidence` admits measured campaign metadata only together with
a structurally checked dependency DAG. This closes the gap between independent
graph validation and exact rebuild-cone campaign validation.
-/

namespace Grass.Build.Manifest

/-- A checked manifest DAG paired with a complete, exact measurement campaign. -/
structure CheckedManifestEvidence (fanout : Nat) (changes : ScenarioChanges) where
  dag : CheckedManifestDag fanout
  campaign : CheckedMeasurementCampaign dag.graph changes

/-- Jointly validate generated graph shape and its measured campaign. -/
def checkManifestEvidence {fanout : Nat} (dag : ManifestDag fanout)
    (changes : ScenarioChanges) (campaign : MeasurementCampaign) :
    Option (CheckedManifestEvidence fanout changes) :=
  match checkManifestDag dag with
  | none => none
  | some checkedDag =>
    match checkMeasurementCampaign checkedDag.graph changes campaign with
    | none => none
    | some checkedCampaign => some ⟨checkedDag, checkedCampaign⟩

/-- `checkManifestEvidence_isSome_iff` characterizes joint admission exactly. -/
theorem checkManifestEvidence_isSome_iff {fanout : Nat}
    (dag : ManifestDag fanout) (changes : ScenarioChanges)
    (campaign : MeasurementCampaign) :
    (checkManifestEvidence dag changes campaign).isSome = true ↔
      dag.WellFormed ∧ campaign.Complete ∧ campaign.ExactFor dag changes := by
  by_cases wellFormed : dag.WellFormed
  · by_cases complete : campaign.Complete
    · by_cases exact : campaign.ExactFor dag changes
      · simp [checkManifestEvidence, checkManifestDag,
          checkMeasurementCampaign, wellFormed, complete, exact]
      · simp [checkManifestEvidence, checkManifestDag,
          checkMeasurementCampaign, wellFormed, complete, exact]
    · simp [checkManifestEvidence, checkManifestDag,
        checkMeasurementCampaign, wellFormed, complete]
  · simp [checkManifestEvidence, checkManifestDag, wellFormed]

/-- Successful joint admission exposes the checked graph ordering invariant. -/
theorem CheckedManifestEvidence.dagWellFormed {fanout : Nat}
    {changes : ScenarioChanges}
    (evidence : CheckedManifestEvidence fanout changes) :
    evidence.dag.graph.WellFormed :=
  evidence.dag.wellFormed

/-- Successful joint admission exposes complete scenario coverage. -/
theorem CheckedManifestEvidence.campaignComplete {fanout : Nat}
    {changes : ScenarioChanges}
    (evidence : CheckedManifestEvidence fanout changes) :
    evidence.campaign.campaign.Complete :=
  evidence.campaign.complete

/-- Successful joint admission exposes exact per-run rebuild cones. -/
theorem CheckedManifestEvidence.campaignExact {fanout : Nat}
    {changes : ScenarioChanges}
    (evidence : CheckedManifestEvidence fanout changes) :
    evidence.campaign.campaign.ExactFor evidence.dag.graph changes :=
  evidence.campaign.exact

end Grass.Build.Manifest
