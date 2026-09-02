import Grass.Process.Cancellation.Policy

/-!
# Cancellation invalidation is local

The two fixtures `agent-bus` disposition `coord1:6` requires:

> add fixtures for local invalidation and a newly discovered blocking call
> rejecting the old certificate.

Two scopes: a `listener` that polls and accepts, and a `writer` that sends. Each
has its own certificate. The fixtures then show the property that makes the
scope-indexed form worth having over the whole-plan one — that discovering a new
blocking call in the listener rejects *the listener's* certificate and leaves
the writer's alone.

Under a whole-plan `callsExact`, the second half would be false: one added
`Sleep` would invalidate every cancellation proof in the program.
-/

namespace Grass.Process.Tests.Cancellation

open Grass.Process
open Grass.Specification (ScopeId)

/-! ## Two scopes -/

@[reducible] def listenerScope : ScopeId := ⟨["Server", "Listener"]⟩
@[reducible] def writerScope : ScopeId := ⟨["Server", "Writer"]⟩

@[reducible] def beforeAcceptPoll : CancellationPointId := ⟨listenerScope, "beforeAcceptPoll"⟩
@[reducible] def pollAccept : BlockingCallId := ⟨listenerScope, "pollAccept"⟩
/-- The call discovered later, by adding a retry loop. -/
@[reducible] def sleepBackoff : BlockingCallId := ⟨listenerScope, "sleepBackoff"⟩

@[reducible] def afterWritable : CancellationPointId := ⟨writerScope, "afterWritable"⟩
@[reducible] def sendPrefix : BlockingCallId := ⟨writerScope, "sendPrefix"⟩

/-- The listener as first discovered: one point, one blocking call. -/
def listenerSummary : ProcessScopeSummary where
  scope := listenerScope
  publicCancellationPoints := [beforeAcceptPoll]
  blockingCalls := [pollAccept]
  pointsDistinct := by simp
  callsDistinct := by simp

/-- The listener after a retry loop is added: the same point, one more call. -/
def listenerSummaryAfterEdit : ProcessScopeSummary where
  scope := listenerScope
  publicCancellationPoints := [beforeAcceptPoll]
  blockingCalls := [pollAccept, sleepBackoff]
  pointsDistinct := by simp
  callsDistinct := by simp

/-- The writer, untouched by that edit. -/
def writerSummary : ProcessScopeSummary where
  scope := writerScope
  publicCancellationPoints := [afterWritable]
  blockingCalls := [sendPrefix]
  pointsDistinct := by simp
  callsDistinct := by simp

/-! ## Their certificates -/

@[reducible] def atPoint (point : CancellationPointId) : CancellationPointPolicy :=
  ⟨point, .uncancellable, .cancellationPoint⟩

/-- The listener's original policy: its one call is cancellable at its one point. -/
def listenerPolicy : CancellationPolicy where
  points := [beforeAcceptPoll]
  pointPolicy := atPoint
  atomicRegions := []
  blockingCalls := [pollAccept]
  callDisposition := fun _ => .cancellableAt beforeAcceptPoll

def listenerCertificate : ScopedCancellationCertificate listenerSummary where
  policy := listenerPolicy
  exact := ⟨rfl, rfl⟩
  regionsDeclared := by
    intro call _ region disposition
    simp [listenerPolicy] at disposition
  pointsDeclared := by
    intro call _ point disposition
    simp [listenerPolicy] at disposition
    simp [listenerPolicy, disposition]

def writerPolicy : CancellationPolicy where
  points := [afterWritable]
  pointPolicy := atPoint
  atomicRegions := []
  blockingCalls := [sendPrefix]
  callDisposition := fun _ => .cancellableAt afterWritable

def writerCertificate : ScopedCancellationCertificate writerSummary where
  policy := writerPolicy
  exact := ⟨rfl, rfl⟩
  regionsDeclared := by
    intro call _ region disposition
    simp [writerPolicy] at disposition
  pointsDeclared := by
    intro call _ point disposition
    simp [writerPolicy] at disposition
    simp [writerPolicy, disposition]

/-! ## Fixture 1 — a newly discovered blocking call rejects the old certificate

The listener gains a `sleepBackoff` call. Its existing policy classified only
`pollAccept`, so it no longer covers the scope. This is `callsExact` doing its
work: the edit is *rejected*, not silently absorbed.
-/

theorem new_call_rejects_old_policy :
    ¬ listenerPolicy.Covers listenerSummaryAfterEdit :=
  CancellationPolicy.not_covers_of_unclassified
    (call := sleepBackoff) (by simp [listenerSummaryAfterEdit])
    (by simp [listenerPolicy])

/-- So the old certificate cannot be reused for the edited scope at all. -/
theorem no_reuse_of_old_certificate
    (attempt : ScopedCancellationCertificate listenerSummaryAfterEdit)
    (samePolicy : attempt.policy = listenerPolicy) : False :=
  new_call_rejects_old_policy (samePolicy ▸ attempt.exact)

/-! ## Fixture 2 — local invalidation

The writer's certificate is a certificate for `writerSummary`, and the listener's
edit did not touch `writerSummary`. So it still stands, and it stands *by
construction* rather than by re-proof: nothing in it mentions the listener.

Stating it as an equality of the underlying policy is the honest form. The
interesting content is not that the term still elaborates — of course it does —
but that its type never mentioned the scope that changed, which is what a
whole-plan `callsExact` would have destroyed.
-/

theorem writer_certificate_unaffected :
    writerCertificate.policy.Covers writerSummary := writerCertificate.exact

/--
The writer's policy never mentions any listener call, so no listener edit can
reach it.

This is the property a whole-plan policy could not have: there, the single
`blockingCalls` list would contain `pollAccept` and `sendPrefix` together, and
adding `sleepBackoff` would change the one list every certificate compares
against.
-/
theorem writer_policy_mentions_no_listener_call :
    pollAccept ∉ writerPolicy.blockingCalls ∧
      sleepBackoff ∉ writerPolicy.blockingCalls := by
  constructor <;> simp [writerPolicy]

/-! ## Composition is a fold, not a monolith

Whole-plan cancellation is the composition of the two scoped certificates, per
`coord1:6`. The composed policy covers the composed summary, and that is proved
from the two child exactness facts rather than by re-checking the program.
-/

theorem scopes_are_compatible :
    ScopedCancellationCertificate.Compatible listenerSummary writerSummary := by
  intro equal
  simp [listenerSummary, writerSummary, listenerScope, writerScope] at equal

theorem composed_policy_covers_composed_summary
    (pointsDistinct :
      (listenerSummary.publicCancellationPoints ++
        writerSummary.publicCancellationPoints).Nodup)
    (callsDistinct :
      (listenerSummary.blockingCalls ++ writerSummary.blockingCalls).Nodup) :
    (ScopedCancellationCertificate.composePolicy listenerPolicy writerPolicy).Covers
      (ScopedCancellationCertificate.composeSummary listenerSummary writerSummary
        scopes_are_compatible pointsDistinct callsDistinct ⟨["Server"]⟩) :=
  ScopedCancellationCertificate.composePolicy_covers
    listenerCertificate.exact writerCertificate.exact scopes_are_compatible
    pointsDistinct callsDistinct ⟨["Server"]⟩

end Grass.Process.Tests.Cancellation
