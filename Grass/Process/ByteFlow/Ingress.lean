import Grass.Process.Cancellation.Identity

/-!
# Byte ingress: where every byte is, at every moment

`docs/PROCESS.md` §3 replaces the fiction that one API call transfers one
requested buffer with an ordered stream and an explicit partition of it:

> Reads and writes are standardized as asynchronous byte-flow processes, not as
> the fiction that one API call transfers one requested buffer. The logical
> payload is an ordered stream of bytes; physical completion boundaries are not
> part of that stream's meaning.

The whole subject is one invariant: every byte the provider has produced is, in
order, either consumed by the parser, held by the parser, in channel escrow, in
the adapter queue, or in flight. `Conserves` below is that, and every transition
preserves it.

## The declared theorem has no content, and this one does

§3 states the exit criterion as

```text
theorem ingress_transition_preserves_conservation
    (step : ByteIngressTransition before after) : after.conservation
```

with `conservation` a *field* of `ByteIngressState`. So `after.conservation` is
a projection, and the theorem is discharged by writing it — it says nothing
about the step at all. `egress_partial_conservation` in the same block is the
same shape: it restates the field it concludes about.

Making the invariant a field is not wrong, but it moves the obligation into
whoever constructs the state and leaves the transition family unchecked. So here
`Conserves` is a *predicate*, the state carries no proof, and
`preserves_conservation` quantifies over the family — which is what
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §5's exit criterion means when it asks for
the theorem "over the full transition family".
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.19 records the defect.

## What is parameterised, and why

`Byte`, the read occurrence, and `ReadBufferLoan` are absent from this tree:
bytes are `Grass.Std.Logical`'s and loans are `Grass.Memory`'s, and
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.1 anticipated exactly this and
prescribed the answer — "the byte-flow modules are parameterized over an
abstract loan type and the instantiation is a named M3 exit item, not a silent
substitution". This module follows that instruction rather than inventing a
placeholder loan.

Sequences are `List Byte` rather than §3's `Vec Byte` for the same reason, and
that one is a genuine simplification to revisit: `Vec` carries a length, which a
capacity-aware rechunking law will want.

## `providerProgress` is not one of §3's constructors

§3's family has `pending` and `readiness`, both of which set `after = before`,
and lets bytes enter only through a resolution's `transferred`. Under that
family `InFlightCompletedBytes phase` is always empty, and the term §3 puts in
its own partition is dead.

A provider filling a loaned buffer is a real event, so `providerProgress` is
here: it grows what the provider has produced and what is in flight, together,
which is exactly what keeps the invariant true while a read is still open. If
the intended reading is that no such step exists, then the partition should lose
its in-flight term, and that is a corpus question rather than something to
resolve by writing whichever is convenient.
-/

namespace Grass.Process

universe u

/-- How an ingress stream ended. -/
inductive IngressTerminalOutcome
  /-- The provider signalled end of stream. -/
  | endOfStream
  /-- The provider failed. -/
  | failed
  /-- A cancellation was acknowledged. -/
  | cancelled (reason : CancelReason)
  deriving Repr

/--
Where an ingress flow is.

`docs/PROCESS.md` §3's phases, with `cancelling` among them — which is the
reason byte flow is M3 rather than M2: the phases are a cancellation race, and
`draining` versus `terminal` is the distinction that keeps a cancelled read from
being treated as finished before its buffers are empty.
-/
inductive ByteIngressPhase (Occurrence : Type u) (Loan : Occurrence → Type u)
  /-- No read outstanding. -/
  | idle
  /-- A read is open, against this loan. -/
  | inFlight (occurrence : Occurrence) (loan : Loan occurrence)
  /-- A cancellation has been requested but not yet resolved. -/
  | cancelling (occurrence : Occurrence) (loan : Loan occurrence) (reason : CancelReason)
  /-- The stream has ended, and the internal buffers are still draining. -/
  | draining (outcome : IngressTerminalOutcome)
  /-- Ended, and empty. -/
  | terminal (outcome : IngressTerminalOutcome)

namespace ByteIngressPhase

/--
The stream is over.

Needed by the buffer-moving transitions below. An earlier draft gave `enqueue`,
`deliver` and `consume` no phase precondition at all, which meant they could
step from a terminal state — so `no_step_after_terminal` was false of the family
and the gap was invisible until that theorem was attempted. Writing the theorem
is what found it.
-/
def Ended {Occurrence : Type u} {Loan : Occurrence → Type u} :
    ByteIngressPhase Occurrence Loan → Prop
  | .terminal _ => True
  | _ => False

@[simp] theorem ended_terminal {Occurrence : Type u} {Loan : Occurrence → Type u}
    (outcome : IngressTerminalOutcome) :
    (ByteIngressPhase.terminal (Occurrence := Occurrence) (Loan := Loan)
      outcome).Ended := trivial

@[simp] theorem not_ended_draining {Occurrence : Type u} {Loan : Occurrence → Type u}
    (outcome : IngressTerminalOutcome) :
    ¬ (ByteIngressPhase.draining (Occurrence := Occurrence) (Loan := Loan)
      outcome).Ended := fun ended => ended

end ByteIngressPhase

/--
The whole state of an ingress flow.

The five byte sequences are the five places a produced byte can be, in stream
order: consumed by the parser, held by the parser, in channel escrow, in the
adapter queue, or written into the open loan and not yet resolved.

No `conservation` field; see the module note. `Conserves` is the invariant and
`preserves_conservation` is the theorem.
-/
structure ByteIngressState (Byte : Type u) (Occurrence : Type u)
    (Loan : Occurrence → Type u) where
  /-- Where the flow is. -/
  phase : ByteIngressPhase Occurrence Loan
  /-- Everything the provider has produced, oldest first. -/
  providerProduced : List Byte
  /-- The prefix the parser has already consumed. -/
  parserConsumed : List Byte
  /-- What the parser holds and has not consumed. -/
  parserRemainder : List Byte
  /-- What the channel is holding in escrow. -/
  channelEscrow : List Byte
  /-- What the adapter has queued but not yet handed to the channel. -/
  adapterQueue : List Byte
  /-- What is written into the open loan and not yet resolved. -/
  inFlightCompleted : List Byte

namespace ByteIngressState

variable {Byte Occurrence : Type u} {Loan : Occurrence → Type u}

/--
**Every produced byte is in exactly one place, and in order.**

`docs/PROCESS.md` §3's `ExactOrderedIngressPartition`. Concatenation rather than
a multiset union is the content: bytes are a stream, so a partition that got the
*order* wrong would still satisfy a counting law and would be wrong.
-/
def Conserves (state : ByteIngressState Byte Occurrence Loan) : Prop :=
  state.providerProduced =
    state.parserConsumed ++ state.parserRemainder ++ state.channelEscrow ++
      state.adapterQueue ++ state.inFlightCompleted

/-- A flow that has produced nothing conserves trivially. -/
theorem conserves_empty (phase : ByteIngressPhase Occurrence Loan) :
    (ByteIngressState.mk phase ([] : List Byte) [] [] [] [] []).Conserves := rfl

end ByteIngressState

/--
One step of an ingress flow.

Each byte-moving constructor is stated as an *equation* on the whole state
rather than as a call to an update function, so that what moved is visible at
the constructor and `preserves_conservation` is a proof about the family rather
than about a definition elsewhere.
-/
inductive ByteIngressTransition {Byte Occurrence : Type u} {Loan : Occurrence → Type u} :
    ByteIngressState Byte Occurrence Loan → ByteIngressState Byte Occurrence Loan → Prop
  /-- A read is started against a fresh loan. Bytes do not move. -/
  | start {before after} {occurrence : Occurrence} {loan : Loan occurrence}
      (idle : before.phase = .idle)
      (exact : after = { before with phase := .inFlight occurrence loan }) :
      ByteIngressTransition before after
  /--
  The provider writes into the open loan.

  The only way bytes enter the flow while a read is open. See the module note on
  why this constructor is here and not in §3's list.
  -/
  | providerProgress {before after} {produced : List Byte}
      {occurrence : Occurrence} {loan : Loan occurrence}
      (open' : before.phase = .inFlight occurrence loan)
      (exact : after =
        { before with
          providerProduced := before.providerProduced ++ produced
          inFlightCompleted := before.inFlightCompleted ++ produced }) :
      ByteIngressTransition before after
  /-- Waiting. Nothing changes, which is `docs/PROCESS.md` §3's `pending`. -/
  | pending {before after} {occurrence : Occurrence} {loan : Loan occurrence}
      (open' : before.phase = .inFlight occurrence loan)
      (exact : after = before) : ByteIngressTransition before after
  /-- A cancellation is requested. The read stays open and the bytes stay put. -/
  | requestCancel {before after} {occurrence : Occurrence} {loan : Loan occurrence}
      {reason : CancelReason}
      (open' : before.phase = .inFlight occurrence loan)
      (exact : after = { before with phase := .cancelling occurrence loan reason }) :
      ByteIngressTransition before after
  /--
  The read resolves: what was in flight becomes queued.

  This is the transition that would silently lose a partial read if the
  in-flight bytes were dropped rather than moved, which is why the equation
  names both sides.
  -/
  | resolveActive {before after} {outcome : IngressTerminalOutcome}
      {occurrence : Occurrence} {loan : Loan occurrence}
      (open' : before.phase = .inFlight occurrence loan)
      (exact : after =
        { before with
          phase := .draining outcome
          adapterQueue := before.adapterQueue ++ before.inFlightCompleted
          inFlightCompleted := [] }) :
      ByteIngressTransition before after
  /--
  And the same, resolving against an outstanding cancellation.

  A separate constructor rather than a disjunction inside one, for the reason
  `Grass/Process/Network/Transition.lean` keeps its ten escrow endings separate:
  which one happened is what a routing-coverage claim is about.
  -/
  | resolveCancellation {before after} {outcome : IngressTerminalOutcome}
      {occurrence : Occurrence} {loan : Loan occurrence} {reason : CancelReason}
      (cancelling' : before.phase = .cancelling occurrence loan reason)
      (exact : after =
        { before with
          phase := .draining outcome
          adapterQueue := before.adapterQueue ++ before.inFlightCompleted
          inFlightCompleted := [] }) :
      ByteIngressTransition before after
  /-- A chunk moves from the adapter queue into channel escrow. -/
  | enqueue {before after} {chunk rest : List Byte}
      (splits : before.adapterQueue = chunk ++ rest)
      (nonempty : chunk ≠ [])
      (live : ¬ before.phase.Ended)
      (exact : after =
        { before with
          channelEscrow := before.channelEscrow ++ chunk
          adapterQueue := rest }) :
      ByteIngressTransition before after
  /-- A chunk is delivered from escrow to the parser. -/
  | deliver {before after} {chunk rest : List Byte}
      (splits : before.channelEscrow = chunk ++ rest)
      (nonempty : chunk ≠ [])
      (live : ¬ before.phase.Ended)
      (exact : after =
        { before with
          parserRemainder := before.parserRemainder ++ chunk
          channelEscrow := rest }) :
      ByteIngressTransition before after
  /-- The parser consumes a prefix of what it holds. -/
  | consume {before after} {chunk rest : List Byte}
      (splits : before.parserRemainder = chunk ++ rest)
      (nonempty : chunk ≠ [])
      (live : ¬ before.phase.Ended)
      (exact : after =
        { before with
          parserConsumed := before.parserConsumed ++ chunk
          parserRemainder := rest }) :
      ByteIngressTransition before after
  /--
  Draining finishes, and only when every internal buffer is empty.

  `docs/PROCESS.md` §3's `IngressInternalBuffersEmpty`. Without it a flow could
  reach `terminal` holding undelivered bytes, and the conservation invariant
  would still hold while the stream had silently lost its tail.
  -/
  | terminate {before after} {outcome : IngressTerminalOutcome}
      (draining : before.phase = .draining outcome)
      (queueEmpty : before.adapterQueue = [])
      (escrowEmpty : before.channelEscrow = [])
      (parserEmpty : before.parserRemainder = [])
      (inFlightEmpty : before.inFlightCompleted = [])
      (exact : after = { before with phase := .terminal outcome }) :
      ByteIngressTransition before after

namespace ByteIngressTransition

variable {Byte Occurrence : Type u} {Loan : Occurrence → Type u}
  {before after : ByteIngressState Byte Occurrence Loan}

/--
**Conservation is preserved, over the whole family.**

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §5's exit criterion, in the form that has
content: the invariant is a predicate rather than a field, so this is a fact
about every constructor rather than a projection.

Each byte-moving case is `List.append_assoc` — moving a chunk from one segment
to the adjacent one leaves the concatenation alone, which is exactly what "no
fabrication, duplication or loss" means for an ordered stream.
-/
theorem preserves_conservation (step : ByteIngressTransition before after)
    (conserved : before.Conserves) : after.Conserves := by
  cases step with
  | start _ exact => subst exact; exact conserved
  | pending _ exact => subst exact; exact conserved
  | requestCancel _ exact => subst exact; exact conserved
  | terminate _ _ _ _ _ exact => subst exact; exact conserved
  | providerProgress _ exact =>
    subst exact
    simp only [ByteIngressState.Conserves] at conserved ⊢
    rw [conserved]
    simp [List.append_assoc]
  | resolveActive _ exact =>
    subst exact
    simp only [ByteIngressState.Conserves] at conserved ⊢
    rw [conserved]
    simp [List.append_assoc]
  | resolveCancellation _ exact =>
    subst exact
    simp only [ByteIngressState.Conserves] at conserved ⊢
    rw [conserved]
    simp [List.append_assoc]
  | enqueue splits _ _ exact =>
    subst exact
    simp only [ByteIngressState.Conserves] at conserved ⊢
    rw [conserved, splits]
    simp [List.append_assoc]
  | deliver splits _ _ exact =>
    subst exact
    simp only [ByteIngressState.Conserves] at conserved ⊢
    rw [conserved, splits]
    simp [List.append_assoc]
  | consume splits _ _ exact =>
    subst exact
    simp only [ByteIngressState.Conserves] at conserved ⊢
    rw [conserved, splits]
    simp [List.append_assoc]

/--
**Nothing steps after the stream is over.**

`docs/PROCESS.md` §3's `no_ingress_step_after_terminal`. Every constructor
requires a phase that `terminal` is not — either by naming the phase it steps
from, or through the `live` hypothesis on the buffer movers — so a terminal flow
has no successor at all and a late completion cannot reopen it.

An earlier draft of the family gave `enqueue`, `deliver`, `consume` and the
resolutions no phase precondition, and this theorem was simply false of it.
Attempting the proof is what found that; nothing else would have, because a
buffer-moving step from a terminal state still conserves.
-/
theorem no_step_after_terminal {outcome : IngressTerminalOutcome}
    (ended : before.phase = .terminal outcome)
    (step : ByteIngressTransition before after) : False := by
  cases step with
  | start idle _ => rw [ended] at idle; exact absurd idle (by simp)
  | providerProgress open' _ => rw [ended] at open'; exact absurd open' (by simp)
  | pending open' _ => rw [ended] at open'; exact absurd open' (by simp)
  | requestCancel open' _ => rw [ended] at open'; exact absurd open' (by simp)
  | terminate draining _ _ _ _ _ =>
    rw [ended] at draining; exact absurd draining (by simp)
  | resolveActive open' _ => rw [ended] at open'; exact absurd open' (by simp)
  | resolveCancellation cancelling' _ =>
    rw [ended] at cancelling'; exact absurd cancelling' (by simp)
  | enqueue _ _ live _ => exact live (ended ▸ trivial)
  | deliver _ _ live _ => exact live (ended ▸ trivial)
  | consume _ _ live _ => exact live (ended ▸ trivial)

end ByteIngressTransition

end Grass.Process
