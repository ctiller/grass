import Grass.Refinement.Console.WriteFileHistory
import Grass.Platform.Win32.WriteFileReturn
import Grass.Std.Console.WriteAll

/-! Conditional caller-policy classification of one exact matched return.
The write-all kernel is reused; its emission witness is already accounted for
by the aligned provider history and is NEVER published again here. Logical
terminal histories below are specification-side consequences, not executed
caller instructions, fresh retry calls, or actual process/status observations.
-/

namespace Grass.Refinement.Console.WriteFileHistory

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Std.Console Grass.Op
open Grass.Platform.Win32.WriteFile

variable {R Outcome Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : CapturedSpecification resources Outcome}
  {projection : CapturedTargetProjection spec Status}
  {realization : Realization} {initial before after : CallProtocol.State Request}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
  {frontier : Prefix before call record}
  {history : History realization initial call record frontier}
  {relation : HandoffRelation projection}

/-- This caller issues writes only while output remains. That is a call-site
premise, not a restriction on generic zero-length Windows WriteFile requests. -/
structure Returned (aligned : Aligned relation history) (selected : ReturnInterpretation)
    (result : ReturnResult) (after : CallProtocol.State Request) : Prop where
  matched : MatchedReturn selected history result after
  nonempty : aligned.start.cut.offset < projection.target.payload.length

namespace Returned

variable {aligned : Aligned relation history} {selected : ReturnInterpretation} {result : ReturnResult}

def cursor (_returned : Returned aligned selected result after) : WriteCursor projection.target.payload :=
  ⟨aligned.start.cut.offset, aligned.start.cut.bounded⟩

/-- Semantic accepted-prefix witness; failure never obtains this count from a DWORD. -/
def count (returned : Returned aligned selected result after) : WriteCount returned.cursor :=
  ⟨frontier.accepted, by
    have bounded := frontier.bounded
    rw [aligned.start.suffix] at bounded
    exact bounded⟩

def response (returned : Returned aligned selected result after) : WriteResponse returned.cursor :=
  if result.rawBool = 0 then .failure returned.count else .success returned.count

/-- The existing portable kernel selects the conditional continuation policy. -/
def decision (returned : Returned aligned selected result after) : WriteNext projection.target.payload :=
  respond returned.cursor returned.nonempty returned.response

/-- On success, the semantic count is the exact initialized reported value. -/
theorem success_count (returned : Returned aligned selected result after) (success : result.rawBool ≠ 0) :
    ∃ value, result.reportedCount = some value ∧
      DwordAt before.machine.memory record.request.countSlot value ∧ value.toNat = returned.count.value := by
  obtain ⟨value, reported, observed, accepted, _⟩ := returned.matched.conforms.success success
  exact ⟨value, reported, observed, accepted⟩

theorem failure_no_count (returned : Returned aligned selected result after) (failure : result.rawBool = 0) :
    result.reportedCount = none := returned.matched.conforms.failure failure

/-- Kernel accounting denotes the already-published provider prefix, not new output. -/
theorem response_emitted (returned : Returned aligned selected result after) :
    returned.response.emitted = frontier.output := by
  unfold response
  split <;> simp only [WriteResponse.emitted, count, cursor, WriteCursor.remaining,
    Prefix.output, aligned.start.suffix, OutputCut.remaining]

def decisionCut (returned : Returned aligned selected result after) : OutputCut projection.target.payload :=
  ⟨returned.decision.cursor.committed, returned.decision.cursor.within⟩

/-- Every kernel branch ends at the SAME globally accounted provider cut. -/
theorem decisionCut_exact (returned : Returned aligned selected result after) :
    returned.decisionCut = aligned.endpoint := by
  apply OutputCut.emitted_injective
  have accounting := respond_prefix_exact returned.cursor returned.nonempty returned.response
  rw [returned.response_emitted] at accounting
  exact accounting.trans (WriteFileProjection.prefix_exact aligned.start.cut aligned.start.suffix frontier)

/-- Failure includes an already fully accepted suffix, without consulting its slot. -/
theorem failure_decision (returned : Returned aligned selected result after) (failure : result.rawBool = 0) :
    returned.decision = .done .writeFailed (advance returned.cursor returned.count) := by
  simp [decision, response, failure, respond]

theorem zero_success_decision (returned : Returned aligned selected result after)
    (success : result.rawBool ≠ 0) (zero : frontier.accepted = 0) :
    returned.decision = .done .noProgress returned.cursor := by
  unfold decision response
  rw [if_neg success]
  simp [respond, count, zero]

theorem partial_success_decision (returned : Returned aligned selected result after)
    (success : result.rawBool ≠ 0) (positive : 0 < frontier.accepted)
    (proper : aligned.endpoint.offset < projection.target.payload.length) :
    returned.decision = .retry (advance returned.cursor returned.count) := by
  have notFull : (advance returned.cursor returned.count).committed ≠ projection.target.payload.length := by
    change aligned.start.cut.offset + frontier.accepted ≠ projection.target.payload.length
    change aligned.start.cut.offset + frontier.accepted < projection.target.payload.length at proper
    omega
  unfold decision response
  rw [if_neg success]
  have nonzero : returned.count.value ≠ 0 := Nat.ne_of_gt positive
  simp only [respond, if_neg nonzero, if_neg notFull]

theorem full_success_decision (returned : Returned aligned selected result after)
    (success : result.rawBool ≠ 0) (full : frontier.accepted = record.request.bytes.length) :
    returned.decision = .done .success (advance returned.cursor returned.count) := by
  have fullCut := aligned.endpoint_full full
  have total : (advance returned.cursor returned.count).committed = projection.target.payload.length :=
    congrArg OutputCut.offset fullCut
  have positive : frontier.accepted ≠ 0 := by
    have more := returned.nonempty
    change aligned.start.cut.offset + frontier.accepted = projection.target.payload.length at total
    omega
  unfold decision response
  rw [if_neg success]
  have nonzero : returned.count.value ≠ 0 := positive
  simp only [respond, if_neg nonzero, if_pos total]

/-- Portable outcomes map to diagnostic causes; stdoutUnavailable is acquisition-only. -/
def cause : WriteOutcome → Behavior.TerminalCause
  | .success => .success
  | .writeFailed => .writeFailed
  | .noProgress => .noProgress

theorem finish_allowed (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) : Behavior.FinishAllowed aligned.endpoint (cause outcome) := by
  have cutEq := congrArg OutputCut.offset returned.decisionCut_exact
  change returned.decision.cursor.committed = aligned.endpoint.offset at cutEq
  rw [done] at cutEq
  change next.committed = aligned.endpoint.offset at cutEq
  cases outcome with
  | success =>
    exact cutEq.symm.trans (respond_success_complete returned.cursor returned.nonempty returned.response next done)
  | writeFailed => trivial
  | noProgress =>
    have proper := (respond_noProgress_unchanged returned.cursor returned.nonempty returned.response next done).2
    change aligned.endpoint.offset < projection.target.payload.length
    exact cutEq ▸ proper

/-- Append only a logical terminal cause to the already-folded upper history. -/
def logicalFinish (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) : projection.system.History :=
  aligned.upper.append (Grass.RelationalSystem.Path.snoc (system := projection.system) .nil
    (.reply aligned.endpoint (.finish (cause outcome))) (.terminal (cause outcome))
    (.finished aligned.endpoint (cause outcome)) ()
    ⟨aligned.upper_located, returned.finish_allowed outcome next done, rfl, rfl⟩)

theorem finish_events (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    (returned.logicalFinish outcome next done).path.events =
      aligned.upper.path.events ++ [.terminal (cause outcome)] := rfl

theorem finish_no_republication (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    Behavior.emittedBytes (returned.logicalFinish outcome next done).path.events =
      Behavior.emittedBytes aligned.upper.path.events := by
  rw [returned.finish_events, Behavior.emittedBytes_append]
  simp [Behavior.emittedBytes]

/-- This complete logical behavior is conditional policy evidence, not physical
caller termination or observed process exit. -/
def logicalComplete (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) : projection.Complete :=
  .terminal (returned.logicalFinish outcome next done)
    ⟨aligned.endpoint, cause outcome, rfl, returned.finish_allowed outcome next done⟩

/-- A retry policy exposes the one remaining suffix at the unchanged upper history;
this tuple constructs no new call, occurrence, physical buffer or instruction step. -/
theorem retry_ready (returned : Returned aligned selected result after)
    (next : WriteCursor projection.target.payload) (retry : returned.decision = .retry next) :
    next.committed = aligned.endpoint.offset ∧ next.remaining = aligned.endpoint.remaining ∧
      next.remaining.length < returned.cursor.remaining.length := by
  have eq := congrArg OutputCut.offset returned.decisionCut_exact
  change returned.decision.cursor.committed = aligned.endpoint.offset at eq
  rw [retry] at eq
  change next.committed = aligned.endpoint.offset at eq
  exact ⟨eq, congrArg (fun n => projection.target.payload.drop n) eq,
    respond_retry_decreases returned.cursor returned.nonempty returned.response next retry⟩

/-- Retry remains proper; completion cannot silently become another write call. -/
theorem retry_proper (returned : Returned aligned selected result after)
    (next : WriteCursor projection.target.payload) (retry : returned.decision = .retry next) :
    aligned.endpoint.offset < projection.target.payload.length := by
  have atEndpoint := (returned.retry_ready next retry).1
  change respond returned.cursor returned.nonempty returned.response = .retry next at retry
  cases responseEq : returned.response with
  | failure count => simp [responseEq, respond] at retry
  | success count =>
    rw [responseEq] at retry
    simp only [respond] at retry
    split at retry
    · contradiction
    · split at retry
      · contradiction
      · cases retry
        have bounded := (advance returned.cursor count).within
        change (advance returned.cursor count).committed = aligned.endpoint.offset at atEndpoint
        omega

/-- Selected public status for this conditional finish, without asserting an
actual OS status observation or distinguishability of the selected mapping. -/
def projectedStatus (_returned : Returned aligned selected result after) (outcome : WriteOutcome)
    (_next : WriteCursor projection.target.payload) (_done : _returned.decision = .done outcome _next) :
    Status := projection.target.status (cause outcome)

end Returned
end Grass.Refinement.Console.WriteFileHistory
