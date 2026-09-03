import Grass.Process.ByteFlow.Ingress

/-!
# Byte egress: offered, committed, and the suffix that must not vanish

`docs/PROCESS.md` §3's egress invariant is one line:

```text
conservation : offered = committed ++ InFlightRequestedBytes phase ++ queued
```

Every byte an author has offered is either committed to the provider, currently
being written, or still queued. `Conserves` below is that, as a predicate rather
than a field, for the reason `Grass/Process/ByteFlow/Ingress.lean` gives and
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.19 records.

## The suffix is the whole difficulty

A write completes with a *prefix* of what was requested. §3:

> Each carries the exact completed prefix plus residual loan/credit/suffix
> disposition; a provider which guarantees zero transfer on one outcome supplies
> that stronger `providerLaw`. No model invents a prior success to account for a
> partial effect.

So a resolution splits the in-flight bytes into a transferred prefix and an
untransferred suffix, and the suffix has to go somewhere. `resolveActive`
returns it to the *front* of the queue, which is what the plan's module table
calls suffix retention, and it is the only placement that both conserves and
keeps the stream in order — appending it to the back would preserve the byte
*count* while silently reordering the caller's stream.

That is the difference between this invariant and a counting one, and the reason
`Conserves` is a concatenation.

## Egress has no draining phase

Ingress needs one: its buffers hold bytes the parser has not seen yet, so
`terminal` must wait for them. Egress does not, because `finish` can simply
require the queue empty and `offered = committed` — everything offered has
already been committed, so there is nothing left to drain. §3's phase list is
asymmetric in exactly this way, and it is asymmetric for a reason rather than by
oversight.
-/

namespace Grass.Process

universe u

/-- How an egress stream ended. -/
inductive EgressTerminalOutcome
  /-- Everything offered was committed and the stream was closed. -/
  | closed
  /-- The provider failed. -/
  | failed
  /-- A cancellation was acknowledged. -/
  | cancelled (reason : CancelReason)
  deriving Repr

/-- Where an egress flow is. -/
inductive ByteEgressPhase (Occurrence : Type u) (Loan : Occurrence → Type u)
  /-- Nothing being written. -/
  | idle
  /-- A write is open, against this loan. -/
  | inFlight (occurrence : Occurrence) (loan : Loan occurrence)
  /-- A cancellation has been requested but not yet resolved. -/
  | cancelling (occurrence : Occurrence) (loan : Loan occurrence) (reason : CancelReason)
  /-- Ended. -/
  | terminal (outcome : EgressTerminalOutcome)

namespace ByteEgressPhase

/-- The stream is over. -/
def Ended {Occurrence : Type u} {Loan : Occurrence → Type u} :
    ByteEgressPhase Occurrence Loan → Prop
  | .terminal _ => True
  | _ => False

@[simp] theorem ended_terminal {Occurrence : Type u} {Loan : Occurrence → Type u}
    (outcome : EgressTerminalOutcome) :
    (ByteEgressPhase.terminal (Occurrence := Occurrence) (Loan := Loan)
      outcome).Ended := trivial

end ByteEgressPhase

/--
The whole state of an egress flow.

Three places an offered byte can be, in stream order: committed, in flight, or
queued.
-/
structure ByteEgressState (Byte : Type u) (Occurrence : Type u)
    (Loan : Occurrence → Type u) where
  /-- Where the flow is. -/
  phase : ByteEgressPhase Occurrence Loan
  /-- Everything the author has offered, oldest first. -/
  offered : List Byte
  /-- The prefix the provider has accepted. -/
  committed : List Byte
  /-- What is currently being written. -/
  inFlightRequested : List Byte
  /-- What is offered and not yet being written. -/
  queued : List Byte

namespace ByteEgressState

variable {Byte Occurrence : Type u} {Loan : Occurrence → Type u}

/-- **Every offered byte is committed, in flight, or queued — in that order.** -/
def Conserves (state : ByteEgressState Byte Occurrence Loan) : Prop :=
  state.offered = state.committed ++ state.inFlightRequested ++ state.queued

/--
**What has been committed is a prefix of what was offered.**

`docs/PROCESS.md` §3's "prefix conservation", derived rather than assumed. A
model that committed bytes the author never offered, or committed them out of
order, could not satisfy `Conserves` — which is the property a provider contract
needs and a counting invariant would not give.
-/
theorem committed_is_a_prefix {state : ByteEgressState Byte Occurrence Loan}
    (conserved : state.Conserves) : state.committed.IsPrefix state.offered :=
  ⟨state.inFlightRequested ++ state.queued, by
    rw [conserved, List.append_assoc]⟩

/-- A flow that has offered nothing conserves trivially. -/
theorem conserves_empty (phase : ByteEgressPhase Occurrence Loan) :
    (ByteEgressState.mk phase ([] : List Byte) [] [] []).Conserves := rfl

end ByteEgressState

/-- One step of an egress flow. -/
inductive ByteEgressTransition {Byte Occurrence : Type u} {Loan : Occurrence → Type u} :
    ByteEgressState Byte Occurrence Loan → ByteEgressState Byte Occurrence Loan → Prop
  /-- The author offers more bytes; they join the back of the queue. -/
  | offer {before after} {chunk : List Byte}
      (nonempty : chunk ≠ [])
      (live : ¬ before.phase.Ended)
      (exact : after =
        { before with
          offered := before.offered ++ chunk
          queued := before.queued ++ chunk }) :
      ByteEgressTransition before after
  /--
  A write starts on a prefix of the queue.

  `nothingInFlight` is required rather than assumed: an idle flow that already
  had bytes in flight would be a state this transition could otherwise silently
  overwrite, losing them.
  -/
  | start {before after} {chunk rest : List Byte}
      {occurrence : Occurrence} {loan : Loan occurrence}
      (idle : before.phase = .idle)
      (nothingInFlight : before.inFlightRequested = [])
      (splits : before.queued = chunk ++ rest)
      (nonempty : chunk ≠ [])
      (exact : after =
        { before with
          phase := .inFlight occurrence loan
          inFlightRequested := chunk
          queued := rest }) :
      ByteEgressTransition before after
  /-- Waiting. -/
  | pending {before after} {occurrence : Occurrence} {loan : Loan occurrence}
      (open' : before.phase = .inFlight occurrence loan)
      (exact : after = before) : ByteEgressTransition before after
  /-- A cancellation is requested. The write stays open. -/
  | requestCancel {before after} {occurrence : Occurrence} {loan : Loan occurrence}
      {reason : CancelReason}
      (open' : before.phase = .inFlight occurrence loan)
      (exact : after = { before with phase := .cancelling occurrence loan reason }) :
      ByteEgressTransition before after
  /--
  The write resolves with a transferred prefix; the suffix returns to the queue.

  The suffix goes to the **front** of the queue. Appending it to the back would
  conserve the byte count and reorder the author's stream, which is the defect a
  concatenation invariant catches and a counting one does not.
  -/
  | resolveActive {before after} {transferred suffix : List Byte}
      {occurrence : Occurrence} {loan : Loan occurrence}
      (open' : before.phase = .inFlight occurrence loan)
      (splits : before.inFlightRequested = transferred ++ suffix)
      (exact : after =
        { before with
          phase := .idle
          committed := before.committed ++ transferred
          inFlightRequested := []
          queued := suffix ++ before.queued }) :
      ByteEgressTransition before after
  /-- And the same against an outstanding cancellation. -/
  | resolveCancellation {before after} {transferred suffix : List Byte}
      {occurrence : Occurrence} {loan : Loan occurrence} {reason : CancelReason}
      (cancelling' : before.phase = .cancelling occurrence loan reason)
      (splits : before.inFlightRequested = transferred ++ suffix)
      (exact : after =
        { before with
          phase := .idle
          committed := before.committed ++ transferred
          inFlightRequested := []
          queued := suffix ++ before.queued }) :
      ByteEgressTransition before after
  /--
  The stream closes, and only when everything offered has been committed.

  `docs/PROCESS.md` §3's `finish` requires `queued = #[]` and
  `offered = committed`. Both, because either alone would let a flow close while
  still holding bytes: an empty queue says nothing about what is in flight.
  -/
  | finish {before after} {outcome : EgressTerminalOutcome}
      (idle : before.phase = .idle)
      (queueEmpty : before.queued = [])
      (nothingInFlight : before.inFlightRequested = [])
      (complete : before.offered = before.committed)
      (exact : after = { before with phase := .terminal outcome }) :
      ByteEgressTransition before after

namespace ByteEgressTransition

variable {Byte Occurrence : Type u} {Loan : Occurrence → Type u}
  {before after : ByteEgressState Byte Occurrence Loan}

/--
**Conservation is preserved, over the whole family.**

The other half of `docs/PROCESS_IMPLEMENTATION_PLAN.md` §5's byte-flow exit
criterion, in the form that has content. The interesting case is `resolveActive`:
the transferred prefix joins `committed` and the untransferred suffix rejoins
the queue, and the concatenation is unchanged only because the suffix goes to
the front.
-/
theorem preserves_conservation (step : ByteEgressTransition before after)
    (conserved : before.Conserves) : after.Conserves := by
  cases step with
  | pending _ exact => subst exact; exact conserved
  | requestCancel _ exact => subst exact; exact conserved
  | finish _ _ _ _ exact => subst exact; exact conserved
  | offer _ _ exact =>
    subst exact
    simp only [ByteEgressState.Conserves] at conserved ⊢
    rw [conserved]
    simp [List.append_assoc]
  | start _ nothingInFlight splits _ exact =>
    subst exact
    simp only [ByteEgressState.Conserves] at conserved ⊢
    rw [conserved, nothingInFlight, splits]
    simp [List.append_assoc]
  | resolveActive _ splits exact =>
    subst exact
    simp only [ByteEgressState.Conserves] at conserved ⊢
    rw [conserved, splits]
    simp [List.append_assoc]
  | resolveCancellation _ splits exact =>
    subst exact
    simp only [ByteEgressState.Conserves] at conserved ⊢
    rw [conserved, splits]
    simp [List.append_assoc]

/--
**Nothing steps after the stream is closed.**

`docs/PROCESS.md` §3's `no_egress_step_after_terminal`. `offer` carries the
`live` hypothesis and every other constructor names the phase it steps from, so
a closed stream has no successor — an author cannot offer bytes to a stream that
has finished, which is the case that would otherwise lose them silently.
-/
theorem no_step_after_terminal {outcome : EgressTerminalOutcome}
    (ended : before.phase = .terminal outcome)
    (step : ByteEgressTransition before after) : False := by
  cases step with
  | offer _ live _ => exact live (ended ▸ trivial)
  | start idle _ _ _ _ => rw [ended] at idle; exact absurd idle (by simp)
  | pending open' _ => rw [ended] at open'; exact absurd open' (by simp)
  | requestCancel open' _ => rw [ended] at open'; exact absurd open' (by simp)
  | resolveActive open' _ _ => rw [ended] at open'; exact absurd open' (by simp)
  | resolveCancellation cancelling' _ _ =>
    rw [ended] at cancelling'; exact absurd cancelling' (by simp)
  | finish idle _ _ _ _ => rw [ended] at idle; exact absurd idle (by simp)

/--
**A closed stream committed everything it was offered.**

The payoff of `finish`'s emptiness conditions: reaching `terminal` from a live
stream means the author's whole stream reached the provider. A `finish` that
checked only the queue would permit closing with bytes still in flight, and this
theorem would be false.

`wasLive` is needed rather than decorative: without it, `offer` and `pending` —
which leave the phase alone — could be steps *from* an already-terminal state,
and the conclusion would not follow from them. It is the same premise
`no_step_after_terminal` makes unnecessary in general, stated locally because
this theorem is about one step rather than about the family.
-/
theorem closed_streams_committed_everything {outcome : EgressTerminalOutcome}
    (step : ByteEgressTransition before after)
    (wasLive : ¬ before.phase.Ended)
    (closes : after.phase = .terminal outcome) :
    after.offered = after.committed := by
  cases step with
  | finish _ _ _ complete exact => subst exact; exact complete
  | offer _ _ exact =>
    rw [exact] at closes
    refine absurd ?_ wasLive
    rw [show before.phase = ByteEgressPhase.terminal outcome from closes]
    trivial
  | pending _ exact =>
    rw [exact] at closes
    refine absurd ?_ wasLive
    rw [show before.phase = ByteEgressPhase.terminal outcome from closes]
    trivial
  | start _ _ _ _ exact => subst exact; exact absurd closes (by simp)
  | requestCancel _ exact => subst exact; exact absurd closes (by simp)
  | resolveActive _ _ exact => subst exact; exact absurd closes (by simp)
  | resolveCancellation _ _ exact => subst exact; exact absurd closes (by simp)

end ByteEgressTransition

end Grass.Process
