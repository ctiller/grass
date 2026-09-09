import Grass.Platform.Win32.WriteFileService
import Grass.Platform.Win32.WriteFileNonresponse

/-!
# Conditional extraction of an infinite WriteFile service continuation

This module consumes a supplied infinite stream of concrete `ServiceReceipt`s.
It does not assert that raw execution supplies such a stream, or classify any
raw transition as a provider service transition.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState

namespace ServiceReceipt

variable {realization : Realization} {call : CallProtocol.CallId}
  {record : CallProtocol.Pending Request}

private def castPrefixPlan {left right : LoanPlan} {state : ProtocolState}
    (same : left = right) (frontier : Prefix left state call record) :
    Prefix right state call record := by
  subst right
  exact frontier

@[simp] private theorem castPrefixPlan_accepted
    {left right : LoanPlan} {state : ProtocolState} (same : left = right)
    (frontier : Prefix left state call record) :
    (castPrefixPlan same frontier).accepted = frontier.accepted := by
  subst right
  rfl

private theorem CommittedStep.reindex
    {realization : Realization} {leftPlan rightPlan : LoanPlan}
    {leftBefore leftAfter rightBefore rightAfter : ProtocolState}
    {leftPre : Prefix leftPlan leftBefore call record}
    {leftPost : Prefix leftPlan leftAfter call record}
    {rightPre : Prefix rightPlan rightBefore call record}
    {rightPost : Prefix rightPlan rightAfter call record}
    {action : Action} {output : Vec Byte}
    (step : CommittedStep realization leftPre leftPost action output)
    (planEq : leftPlan = rightPlan) (beforeEq : leftBefore = rightBefore)
    (afterEq : leftAfter = rightAfter)
    (preAccepted : leftPre.accepted = rightPre.accepted)
    (postAccepted : leftPost.accepted = rightPost.accepted) :
    CommittedStep realization rightPre rightPost action output := by
  subst rightPlan
  subst rightBefore
  subst rightAfter
  refine
    { ran := step.ran
      dispatch := step.dispatch
      publishes := ?_
      publication := ?_
      obligations := step.obligations
      metadata := step.metadata
      confined := step.confined
      causal := step.causal }
  · simpa only [← preAccepted, ← postAccepted] using step.publishes
  · simpa only [← preAccepted, ← postAccepted] using step.publication

/-- Consecutive receipts over the same supplied raw-state stream have the exact
protocol endpoint and runtime entry computed by the preceding receipt. -/
theorem stream_continuity
    (raw : Nat → RawState) (action : Nat → Action) (output : Nat → Vec Byte)
    (receipt : ∀ n, ServiceReceipt realization (raw n) call record (action n) (output n))
    (advances : ∀ n, (receipt n).after = raw (n + 1)) (n : Nat) :
    (receipt (n + 1)).protocol = (receipt n).nextProtocol ∧
      (receipt (n + 1)).runtime = (receipt n).nextRuntime := by
  have protocol : (receipt (n + 1)).protocol = (receipt n).nextProtocol := by
    apply Option.some.inj
    calc
      some (receipt (n + 1)).protocol =
          (raw (n + 1)).metadata.pack? (raw (n + 1)).machine.machine :=
        (receipt (n + 1)).projected.symm
      _ = (receipt n).after.metadata.pack? (receipt n).after.machine.machine := by
        rw [advances n]
      _ = some (receipt n).nextProtocol := (receipt n).after_projected
  have runtime : (receipt (n + 1)).runtime = (receipt n).nextRuntime := by
    apply CallRuntime.writeFile.inj
    apply Option.some.inj
    calc
      some (.writeFile (receipt (n + 1)).runtime) =
          (raw (n + 1)).calls.lookup call := (receipt (n + 1)).runtimeLookup.symm
      _ = (receipt n).after.calls.lookup call := by rw [advances n]
      _ = some (.writeFile (receipt n).nextRuntime) := (receipt n).after_runtimeLookup
  exact ⟨protocol, runtime⟩

/-- The ABI-derived loan plan is constant along the supplied service stream. -/
theorem stream_loanPlan
    (raw : Nat → RawState) (action : Nat → Action) (output : Nat → Vec Byte)
    (receipt : ∀ n, ServiceReceipt realization (raw n) call record (action n) (output n))
    (advances : ∀ n, (receipt n).after = raw (n + 1)) (n : Nat) :
    (receipt n).runtime.loanPlan = (receipt 0).runtime.loanPlan := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have runtime := (stream_continuity raw action output receipt advances n).2
      calc
        (receipt (n + 1)).runtime.loanPlan = (receipt n).nextRuntime.loanPlan :=
          congrArg Grass.Platform.Win32.WriteFileRuntime.loanPlan runtime
        _ = (receipt n).runtime.loanPlan := (receipt n).after_loanPlan
        _ = (receipt 0).runtime.loanPlan := ih

/-- Extract the existing infinite-continuation evidence from a supplied stream
of consecutive service receipts. No equality between the receipts' `Prepared`
witnesses is assumed or proved; `CommittedStep.reindex` changes only those
prefix witnesses while the runtime table fixes the protocol state, plan, and
accepted frontier at every edge. -/
def extractInfiniteContinuation
    (raw : Nat → RawState) (action : Nat → Action) (output : Nat → Vec Byte)
    (receipt : ∀ n, ServiceReceipt realization (raw n) call record (action n) (output n))
    (advances : ∀ n, (receipt n).after = raw (n + 1))
    {initial : ProtocolState}
    (history : History (receipt 0).runtime.loanPlan realization initial call record
      (receipt 0).pre) : InfiniteContinuation history where
  point n := ⟨(receipt n).protocol,
    castPrefixPlan (stream_loanPlan raw action output receipt advances n) (receipt n).pre⟩
  start := rfl
  action := action
  output := output
  committed n := by
    have continuity := stream_continuity raw action output receipt advances n
    have nextAccepted : (receipt n).post.accepted =
        (receipt (n + 1)).pre.accepted := by
      calc
        (receipt n).post.accepted = (receipt n).nextRuntime.accepted :=
          (receipt n).after_accepted.symm
        _ = (receipt (n + 1)).runtime.accepted :=
          congrArg Grass.Platform.Win32.WriteFileRuntime.accepted continuity.2.symm
        _ = (receipt (n + 1)).pre.accepted := (receipt (n + 1)).accepted.symm
    apply CommittedStep.reindex (receipt n).committed
      (stream_loanPlan raw action output receipt advances n) rfl continuity.1.symm
    · simp
    · simpa only [castPrefixPlan_accepted] using nextAccepted

@[simp] theorem extractInfiniteContinuation_point_state
    (raw : Nat → RawState) (action : Nat → Action) (output : Nat → Vec Byte)
    (receipt : ∀ n, ServiceReceipt realization (raw n) call record (action n) (output n))
    (advances : ∀ n, (receipt n).after = raw (n + 1))
    {initial : ProtocolState}
    (history : History (receipt 0).runtime.loanPlan realization initial call record
      (receipt 0).pre) (n : Nat) :
    ((extractInfiniteContinuation raw action output receipt advances history).point n).1 =
      (receipt n).protocol := rfl

@[simp] theorem extractInfiniteContinuation_point_accepted
    (raw : Nat → RawState) (action : Nat → Action) (output : Nat → Vec Byte)
    (receipt : ∀ n, ServiceReceipt realization (raw n) call record (action n) (output n))
    (advances : ∀ n, (receipt n).after = raw (n + 1))
    {initial : ProtocolState}
    (history : History (receipt 0).runtime.loanPlan realization initial call record
      (receipt 0).pre) (n : Nat) :
    ((extractInfiniteContinuation raw action output receipt advances history).point n).2.accepted =
      (receipt n).runtime.accepted := by
  simp [extractInfiniteContinuation, (receipt n).accepted]

@[simp] theorem extractInfiniteContinuation_action
    (raw : Nat → RawState) (action : Nat → Action) (output : Nat → Vec Byte)
    (receipt : ∀ n, ServiceReceipt realization (raw n) call record (action n) (output n))
    (advances : ∀ n, (receipt n).after = raw (n + 1))
    {initial : ProtocolState}
    (history : History (receipt 0).runtime.loanPlan realization initial call record
      (receipt 0).pre) (n : Nat) :
    (extractInfiniteContinuation raw action output receipt advances history).action n = action n := rfl

@[simp] theorem extractInfiniteContinuation_output
    (raw : Nat → RawState) (action : Nat → Action) (output : Nat → Vec Byte)
    (receipt : ∀ n, ServiceReceipt realization (raw n) call record (action n) (output n))
    (advances : ∀ n, (receipt n).after = raw (n + 1))
    {initial : ProtocolState}
    (history : History (receipt 0).runtime.loanPlan realization initial call record
      (receipt 0).pre) (n : Nat) :
    (extractInfiniteContinuation raw action output receipt advances history).output n = output n := rfl

end ServiceReceipt

end Grass.Platform.Win32.WriteFile
