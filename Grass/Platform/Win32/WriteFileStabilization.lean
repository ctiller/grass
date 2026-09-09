import Grass.Platform.Win32.WriteFileNonresponse

variable {plan : Grass.Platform.Win32.WriteFile.LoanPlan}

/-! Every actual infinite WriteFile provider continuation eventually has a
fixed accepted count because its counts are monotone and bounded by the finite
request. `InfiniteContinuation.shift_historyAt` preserves the original history;
`InfiniteContinuation.shift_root_published` retains prior publications. This adds no
responsiveness, dispatch, or caller-normalization claim. -/

namespace Grass.Platform.Win32.WriteFile

open Grass.Op Grass.Std.Logical

private theorem sequence_monotone {f : Nat → Nat}
    (step : ∀ n, f n ≤ f (n + 1)) {i j : Nat} (bounded : i ≤ j) : f i ≤ f j := by
  induction bounded with
  | refl => exact Nat.le_refl _
  | @step j bounded ih => exact Nat.le_trans ih (step j)

private theorem eventually_constant_of_bounded_monotone (bound : Nat) (f : Nat → Nat)
    (bounded : ∀ n, f n ≤ bound) (step : ∀ n, f n ≤ f (n + 1)) :
    ∃ index, ∀ n, f (index + n) = f index := by
  induction bound generalizing f with
  | zero =>
      refine ⟨0, fun n => ?_⟩
      have atN := bounded n
      have atZero := bounded 0
      rw [Nat.zero_add]
      omega
  | succ bound ih =>
      by_cases startPositive : 0 < f 0
      · let reduced : Nat → Nat := fun n => f n - 1
        have reducedBounded : ∀ n, reduced n ≤ bound := by
          intro n
          have positive : 0 < f n := Nat.lt_of_lt_of_le startPositive
            (sequence_monotone step (Nat.zero_le n))
          have upper := bounded n
          simp only [reduced]
          omega
        have reducedStep : ∀ n, reduced n ≤ reduced (n + 1) := by
          intro n
          exact Nat.sub_le_sub_right (step n) 1
        obtain ⟨index, fixed⟩ := ih reduced reducedBounded reducedStep
        refine ⟨index, fun n => ?_⟩
        have positiveLeft : 0 < f (index + n) := Nat.lt_of_lt_of_le startPositive
          (sequence_monotone step (Nat.zero_le _))
        have positiveRight : 0 < f index := Nat.lt_of_lt_of_le startPositive
          (sequence_monotone step (Nat.zero_le _))
        have same := fixed n
        simp only [reduced] at same
        omega
      · have startZero : f 0 = 0 := by omega
        by_cases fixedZero : ∀ n, f n = 0
        · exact ⟨0, fun n => by rw [fixedZero, startZero]⟩
        · have existsChanged : ∃ n, f n ≠ 0 := Classical.not_forall.mp fixedZero
          obtain ⟨shiftAt, changed⟩ := existsChanged
          have shiftedPositive : 0 < f shiftAt := by omega
          let reduced : Nat → Nat := fun n => f (shiftAt + n) - 1
          have reducedBounded : ∀ n, reduced n ≤ bound := by
            intro n
            have upper := bounded (shiftAt + n)
            have positive : 0 < f (shiftAt + n) := Nat.lt_of_lt_of_le shiftedPositive
              (sequence_monotone step (Nat.le_add_right shiftAt n))
            simp only [reduced]
            omega
          have reducedStep : ∀ n, reduced n ≤ reduced (n + 1) := by
            intro n
            apply Nat.sub_le_sub_right _ 1
            simpa [Nat.add_assoc] using step (shiftAt + n)
          obtain ⟨index, fixed⟩ := ih reduced reducedBounded reducedStep
          refine ⟨shiftAt + index, fun n => ?_⟩
          have same := fixed n
          have positiveLeft : 0 < f (shiftAt + (index + n)) :=
            Nat.lt_of_lt_of_le shiftedPositive
              (sequence_monotone step (Nat.le_add_right shiftAt _))
          have positiveRight : 0 < f (shiftAt + index) :=
            Nat.lt_of_lt_of_le shiftedPositive
              (sequence_monotone step (Nat.le_add_right shiftAt _))
          simp only [reduced] at same
          rw [Nat.add_assoc]
          omega

/-- Reindex an actual continuation at its actual derived history. -/
def InfiniteContinuation.shift
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    {history : History plan realization initial call record frontier}
    (continuation : InfiniteContinuation history) (offset : Nat) :
    InfiniteContinuation (continuation.historyAt offset) where
  point n := continuation.point (offset + n)
  start := by simp
  action n := continuation.action (offset + n)
  output n := continuation.output (offset + n)
  committed n := by
    have indexEq : offset + (n + 1) = offset + n + 1 := by omega
    rw [indexEq]
    exact continuation.committed (offset + n)

@[simp] theorem InfiniteContinuation.shift_point
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    {history : History plan realization initial call record frontier}
    (continuation : InfiniteContinuation history) (offset n : Nat) :
    (continuation.shift offset).point n = continuation.point (offset + n) := rfl

@[simp] theorem InfiniteContinuation.shift_action
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    {history : History plan realization initial call record frontier}
    (continuation : InfiniteContinuation history) (offset n : Nat) :
    (continuation.shift offset).action n = continuation.action (offset + n) := rfl

@[simp] theorem InfiniteContinuation.shift_output
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    {history : History plan realization initial call record frontier}
    (continuation : InfiniteContinuation history) (offset n : Nat) :
    (continuation.shift offset).output n = continuation.output (offset + n) := rfl

/-- Reindexing retains the exact accumulated history, including every stored
action, output chunk, and committed-step proof. -/
theorem InfiniteContinuation.shift_historyAt
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    {history : History plan realization initial call record frontier}
    (continuation : InfiniteContinuation history) (offset n : Nat) :
    HEq ((continuation.shift offset).historyAt n)
      (continuation.historyAt (offset + n)) := by
  induction n with
  | zero => simpa using (continuation.shift offset).historyAt_zero
  | succ n ih =>
      rw [InfiniteContinuation.historyAt_succ]
      rw [show offset + (n + 1) = (offset + n) + 1 by omega]
      rw [InfiniteContinuation.historyAt_succ]
      simp only [InfiniteContinuation.shift_action, InfiniteContinuation.shift_output]
      have ihEq := eq_of_heq ih
      rw [ihEq]
      rfl

/-- The shifted root is the actual derived history and therefore retains the
complete output prefix published before the stabilization point. -/
theorem InfiniteContinuation.shift_root_published
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    {history : History plan realization initial call record frontier}
    (continuation : InfiniteContinuation history) (offset : Nat) :
    (continuation.historyAt offset).published = (continuation.point offset).2.output :=
  (continuation.historyAt offset).published_eq_output

/-- Monotone bounded accepted counts stabilize along every supplied actual
infinite provider continuation. -/
theorem InfiniteContinuation.stabilizes
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    {history : History plan realization initial call record frontier}
    (continuation : InfiniteContinuation history) :
    ∃ index, FixedCut (continuation.shift index) := by
  let accepted : Nat → Nat := fun n => (continuation.point n).2.accepted
  have bounded : ∀ n, accepted n ≤ record.request.bytes.length :=
    fun n => (continuation.point n).2.bounded
  have monotone : ∀ n, accepted n ≤ accepted (n + 1) :=
    fun n => (continuation.committed n).publication.monotone
  obtain ⟨index, fixed⟩ := eventually_constant_of_bounded_monotone
    record.request.bytes.length accepted bounded monotone
  refine ⟨index, ⟨fun n => ?_⟩⟩
  exact fixed n

end Grass.Platform.Win32.WriteFile
