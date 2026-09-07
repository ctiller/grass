import Grass.Build.Manifest.Report

/-!
# Threshold-free measured build comparisons

Comparisons report direction and exact magnitude between two observed runs.
They do not turn one sample into a performance guarantee, impose an arbitrary
timing threshold, or claim asymptotic complexity.
-/

namespace Grass.Build.Manifest

/-- Exact directional change between two natural-valued observations. -/
inductive NatChange where
  | decreased (amount : Nat)
  | unchanged
  | increased (amount : Nat)
  deriving DecidableEq, Repr

/-- The arithmetic meaning of a reported directional change. Strict changes
carry positive magnitudes; unchanged values are equal. -/
def NatChange.Describes : NatChange → Nat → Nat → Prop
  | .decreased amount, previous, current =>
      0 < amount ∧ current + amount = previous
  | .unchanged, previous, current => current = previous
  | .increased amount, previous, current =>
      0 < amount ∧ previous + amount = current

instance NatChange.instDecidableDescribes
    (change : NatChange) (previous current : Nat) :
    Decidable (change.Describes previous current) := by
  cases change <;> unfold Describes <;> infer_instance

/-- Compare two observations without selecting a pass/fail budget. -/
def compareNat (previous current : Nat) : NatChange :=
  if _lower : current < previous then
    .decreased (previous - current)
  else if _higher : previous < current then
    .increased (current - previous)
  else
    .unchanged

/-- `compareNat_describes` proves that every computed delta exactly
reconstructs its input observations. -/
theorem compareNat_describes (previous current : Nat) :
    (compareNat previous current).Describes previous current := by
  by_cases lower : current < previous
  · simp [compareNat, lower, NatChange.Describes]
    omega
  · by_cases higher : previous < current
    · simp [compareNat, lower, higher, NatChange.Describes]
      omega
    · have equal : current = previous := Nat.le_antisymm
        (Nat.le_of_not_gt higher) (Nat.le_of_not_gt lower)
      simp [compareNat, NatChange.Describes, equal]

/-- Exact raw deltas between two measured build runs.
`BuildRunComparison.previousScenario` and
`BuildRunComparison.currentScenario` retain both scenarios so a body-edit/no-op
comparison cannot be mistaken for two samples of the same experiment. -/
structure BuildRunComparison where
  previousScenario : BuildScenario
  currentScenario : BuildScenario
  wallNanoseconds : NatChange
  peakResidentBytes : NatChange
  reElaboratedNodes : NatChange
  kernelCheckedDeclarations : NatChange
  oleanBytes : NatChange
  proofBytes : NatChange
  artifactBytes : NatChange
  deriving DecidableEq, Repr

/-- Compute exact directional deltas from retained observations. -/
def compareBuildRuns (previous current : BuildRunReport) : BuildRunComparison :=
  { previousScenario := previous.scenario
    currentScenario := current.scenario
    wallNanoseconds := compareNat previous.wallNanoseconds current.wallNanoseconds
    peakResidentBytes :=
      compareNat previous.peakResidentBytes current.peakResidentBytes
    reElaboratedNodes :=
      compareNat previous.totals.reElaboratedNodes
        current.totals.reElaboratedNodes
    kernelCheckedDeclarations :=
      compareNat previous.totals.kernelCheckedDeclarations
        current.totals.kernelCheckedDeclarations
    oleanBytes := compareNat previous.totals.oleanBytes current.totals.oleanBytes
    proofBytes := compareNat previous.totals.proofBytes current.totals.proofBytes
    artifactBytes :=
      compareNat previous.totals.artifactBytes current.totals.artifactBytes }

/-- Full arithmetic specification of a run comparison. -/
def BuildRunComparison.ExactFor (comparison : BuildRunComparison)
    (previous current : BuildRunReport) : Prop :=
  comparison.previousScenario = previous.scenario ∧
  comparison.currentScenario = current.scenario ∧
  comparison.wallNanoseconds.Describes
    previous.wallNanoseconds current.wallNanoseconds ∧
  comparison.peakResidentBytes.Describes
    previous.peakResidentBytes current.peakResidentBytes ∧
  comparison.reElaboratedNodes.Describes
    previous.totals.reElaboratedNodes current.totals.reElaboratedNodes ∧
  comparison.kernelCheckedDeclarations.Describes
    previous.totals.kernelCheckedDeclarations
    current.totals.kernelCheckedDeclarations ∧
  comparison.oleanBytes.Describes
    previous.totals.oleanBytes current.totals.oleanBytes ∧
  comparison.proofBytes.Describes
    previous.totals.proofBytes current.totals.proofBytes ∧
  comparison.artifactBytes.Describes
    previous.totals.artifactBytes current.totals.artifactBytes

instance BuildRunComparison.instDecidableExactFor
    (comparison : BuildRunComparison) (previous current : BuildRunReport) :
    Decidable (comparison.ExactFor previous current) := by
  unfold ExactFor
  infer_instance

/-- `compareBuildRuns_exact` proves every field of the generated comparison
describes the retained measurements exactly. -/
theorem compareBuildRuns_exact (previous current : BuildRunReport) :
    (compareBuildRuns previous current).ExactFor previous current := by
  simp [compareBuildRuns, BuildRunComparison.ExactFor, compareNat_describes]

end Grass.Build.Manifest
