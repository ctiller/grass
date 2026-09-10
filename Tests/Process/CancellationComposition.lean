import Grass.Process.Cancellation.Policy

/-! Regression coverage for composition of independently checked cancellation
certificates. The fixtures deliberately reuse textual names across scopes: the
scoped identities remain distinct, and right-side dispatch must not be shadowed
by the left policy. -/

namespace Grass.Process.Tests.CancellationComposition

open Grass.Specification (ScopeId)

@[reducible] def leftScope : ScopeId := ⟨["left"]⟩
@[reducible] def rightScope : ScopeId := ⟨["right"]⟩
@[reducible] def aggregateScope : ScopeId := ⟨["aggregate"]⟩

@[reducible] def leftPoint : CancellationPointId := ⟨leftScope, "cancel"⟩
@[reducible] def rightPoint : CancellationPointId := ⟨rightScope, "cancel"⟩
@[reducible] def leftCall : BlockingCallId := ⟨leftScope, "wait"⟩
@[reducible] def rightCall : BlockingCallId := ⟨rightScope, "wait"⟩
@[reducible] def leftRegion : AtomicRegionId := ⟨leftScope, "commit"⟩

def boundedCommit : BoundedAtomicRegion where
  id := leftRegion
  stepBound := 7
  positive := by decide

def pointPolicy (point : CancellationPointId) : CancellationPointPolicy where
  id := point
  entryMask := .cancellationPoint
  exitMask := .uncancellable

def leftSummary : ProcessScopeSummary where
  scope := leftScope
  publicCancellationPoints := [leftPoint]
  blockingCalls := [leftCall]
  pointsDistinct := by decide
  callsDistinct := by decide

def rightSummary : ProcessScopeSummary where
  scope := rightScope
  publicCancellationPoints := [rightPoint]
  blockingCalls := [rightCall]
  pointsDistinct := by decide
  callsDistinct := by decide

def leftPolicy : CancellationPolicy where
  points := [leftPoint]
  pointPolicy := pointPolicy
  atomicRegions := [boundedCommit]
  blockingCalls := [leftCall]
  callDisposition := fun _ => .withinAtomicRegion leftRegion

def rightPolicy : CancellationPolicy where
  points := [rightPoint]
  pointPolicy := pointPolicy
  atomicRegions := []
  blockingCalls := [rightCall]
  callDisposition := fun _ => .cancellableAt rightPoint

def leftCertificate : ScopedCancellationCertificate leftSummary where
  policy := leftPolicy
  exact := ⟨rfl, rfl⟩
  regionsDeclared := by
    intro call inCalls region disposition
    simp only [leftPolicy, List.mem_singleton] at inCalls
    subst call
    simp only [leftPolicy] at disposition
    injection disposition with same
    subst region
    have member : boundedCommit ∈ leftPolicy.atomicRegions := by
      change boundedCommit ∈ [boundedCommit]
      exact List.Mem.head _
    exact ⟨boundedCommit, member, rfl⟩
  pointsDeclared := by
    intro call inCalls point disposition
    simp only [leftPolicy, List.mem_singleton] at inCalls
    subst call
    simp only [leftPolicy] at disposition
    contradiction

def rightCertificate : ScopedCancellationCertificate rightSummary where
  policy := rightPolicy
  exact := ⟨rfl, rfl⟩
  regionsDeclared := by
    intro call inCalls region disposition
    simp only [rightPolicy, List.mem_singleton] at inCalls
    subst call
    simp only [rightPolicy] at disposition
    contradiction
  pointsDeclared := by
    intro call inCalls point disposition
    simp only [rightPolicy, List.mem_singleton] at inCalls
    subst call
    simp only [rightPolicy] at disposition
    injection disposition with same
    subst point
    simp [rightPolicy]

theorem compatible :
    ScopedCancellationCertificate.Compatible leftSummary rightSummary := by
  change leftScope ≠ rightScope
  decide

theorem pointsDistinct :
    (leftSummary.publicCancellationPoints ++
      rightSummary.publicCancellationPoints).Nodup := by
  decide

theorem callsDistinct :
    (leftSummary.blockingCalls ++ rightSummary.blockingCalls).Nodup := by
  decide

def composed := ScopedCancellationCertificate.compose
  leftCertificate rightCertificate compatible pointsDistinct callsDistinct aggregateScope

/-- Equal textual names remain distinct because their scope is part of the id. -/
theorem same_names_are_scoped :
    leftPoint.name = rightPoint.name ∧ leftPoint ≠ rightPoint ∧
      leftCall.name = rightCall.name ∧ leftCall ≠ rightCall := by
  decide

/-- The right call reaches the right policy despite sharing its textual name
with the left call. -/
theorem right_call_resolves_to_right_policy :
    composed.policy.callDisposition rightCall = .cancellableAt rightPoint := by
  rfl

theorem both_point_policies_dispatch_exactly :
    composed.policy.pointPolicy leftPoint = pointPolicy leftPoint ∧
      composed.policy.pointPolicy rightPoint = pointPolicy rightPoint := by
  decide

/-- Composition retains the concrete positive bound of the left atomic region. -/
theorem nonzero_atomic_bound_is_preserved :
    ∃ bounded ∈ composed.policy.atomicRegions,
      bounded.id = leftRegion ∧ bounded.stepBound = 7 ∧ 0 < bounded.stepBound := by
  change ∃ bounded ∈ [boundedCommit] ++ [],
    bounded.id = leftRegion ∧ bounded.stepBound = 7 ∧ 0 < bounded.stepBound
  exact ⟨boundedCommit, by simp, rfl, rfl, boundedCommit.positive⟩

/-- The aggregate is a full certificate, so both declaration laws are retained. -/
theorem composed_certificate_is_well_formed :
    composed.policy.RegionsDeclared ∧ composed.policy.PointsDeclared :=
  ⟨composed.regionsDeclared, composed.pointsDeclared⟩

end Grass.Process.Tests.CancellationComposition
