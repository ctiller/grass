import Grass.Process.Network.Topology

/-!
# Mailboxes, ordering profiles, and selective receive

`docs/PROCESS.md` §3, on the Erlang-derived patterns Grass adopts:

> A channel profile states its ordering guarantee explicitly. The Erlang-shaped
> profile preserves send order only from one sender incarnation to one receiver
> incarnation; it invents no global order between senders. Every signal has a
> fresh occurrence even when payloads are equal. Selective receive consumes the
> oldest matching occurrence while every skipped occurrence retains order,
> escrow, obligations, and resource charge.

Two things in that paragraph are easy to implement wrongly in the same direction
— by accidentally promising more order than the profile does — and this module
is built around not doing that.

## The ordering guarantee is per sender pair, and the gap is the point

`PerSenderPair` says: two messages from *the same* sender incarnation to *the
same* receiver arrive in send order. It says nothing about two messages from
different senders, and `perSenderPair_ignores_interleaving` below is the theorem
that it says nothing: the profile is a function of the per-sender projections
alone, so any two mailboxes that agree on every sender's own subsequence satisfy
it equally, however differently their senders are interleaved. Stated positively,
because a reader who assumes a global order will write a proof that seems to work
and a realization that races.

`docs/FOUNDATION.md` law 18 is the same prohibition from the other side:
delivery interleaving between independent senders is a schedule fact, and a
specification that depended on it would be observing something the realization
is free to change.

## Skipping is not free

`SelectiveReceive` charges `scanWork` for the prefix it scanned past.
`docs/PROCESS.md` §3: "Neither mechanism is free: unbounded mailboxes or
postponed sets fail resource/progress gates." A selective receive that walked a
million-entry mailbox and reported no cost would let a process do unbounded work
inside one transition, which is exactly what the progress argument in
`Grass/Process/Progress.lean` assumes cannot happen.
-/

namespace Grass.Process

universe u w v r

/--
One delivered signal: its occurrence identity and its payload.

The identity is separate from the payload because `docs/PROCESS.md` §3 requires
that "every signal has a fresh occurrence even when payloads are equal". Two
identical messages are two entries, and a receive consumes one of them.
-/
structure MailboxEntry (Carrier : Type r) (SenderId : Type r) (Message : Type w) where
  /-- The occurrence. Fresh per signal; see `Grass/Process/Nominal.lean`. -/
  occurrence : LogicalNominal Carrier
  /-- It is a message occurrence and not some other identity. -/
  isMessage : occurrence.kind = .messageOccurrence
  /-- Which sender incarnation sent it. -/
  sender : SenderId
  /-- What was sent. -/
  payload : Message

/--
A receiver's mailbox: delivered entries, oldest first.

A list and not a set: order is the whole subject. Duplicate-free on occurrence
identity, because the same signal delivered twice would be a fabrication.
-/
structure Mailbox (Carrier : Type r) (SenderId : Type r) (Message : Type w) where
  /-- Delivered entries, oldest first. -/
  entries : List (MailboxEntry Carrier SenderId Message)
  /-- No occurrence appears twice. -/
  distinct : (entries.map MailboxEntry.occurrence).Nodup

namespace Mailbox

variable {Carrier SenderId : Type r} {Message : Type w}

/-- The empty mailbox. -/
def empty : Mailbox Carrier SenderId Message where
  entries := []
  distinct := by simp

/-- How many signals are waiting. -/
def size (mailbox : Mailbox Carrier SenderId Message) : Nat := mailbox.entries.length

/-- The entries from one sender incarnation, in arrival order. -/
def from' [DecidableEq SenderId] (mailbox : Mailbox Carrier SenderId Message)
    (sender : SenderId) : List (MailboxEntry Carrier SenderId Message) :=
  mailbox.entries.filter (fun entry => entry.sender == sender)

/--
**The ordering guarantee: per sender pair, and no further.**

This mailbox belongs to one receiver incarnation, so "same receiver" is already
fixed by which mailbox it is. The profile therefore says: entries from one
sender appear in the order that sender sent them.

Strictly increasing send order along each sender's own subsequence, written with
`List.Pairwise` rather than with indices. An earlier version quantified over
positions, which made the very theorem this definition exists to support -
`perSenderPair_ignores_interleaving` - unprovable, because the index bounds are
dependent on the list and do not survive rewriting it.

Stated as a property of a delivery rather than as a field, because it is a claim
a channel realization discharges, not a structure a mailbox carries.
-/
def PerSenderPair [DecidableEq SenderId]
    (sendOrder : MailboxEntry Carrier SenderId Message → Nat)
    (mailbox : Mailbox Carrier SenderId Message) : Prop :=
  ∀ sender, (((mailbox.from' sender).map sendOrder).Pairwise (· < ·))

/--
**The profile ignores interleaving between senders.**

`PerSenderPair` reads only `from' sender`, so two mailboxes agreeing on every
sender's own subsequence satisfy it or fail it together — no matter how those
subsequences are interleaved with each other.

This is the negative half of the guarantee made checkable. A realization may
deliver A's messages and B's in any interleaving it likes; a specification that
depended on one would be observing a schedule fact, which `docs/FOUNDATION.md`
law 18 makes replaceable.
-/
theorem perSenderPair_ignores_interleaving [DecidableEq SenderId]
    (sendOrder : MailboxEntry Carrier SenderId Message → Nat)
    (left right : Mailbox Carrier SenderId Message)
    (samePerSender : ∀ sender, left.from' sender = right.from' sender) :
    PerSenderPair sendOrder left ↔ PerSenderPair sendOrder right := by
  constructor
  · intro holds sender
    rw [← samePerSender sender]
    exact holds sender
  · intro holds sender
    rw [samePerSender sender]
    exact holds sender

end Mailbox

/--
The result of a selective receive: the oldest matching entry, what remains, and
what it cost to find.

`docs/PROCESS.md` §3's `SelectiveReceive`, with `scanWork` kept as a field
rather than derived, because it is a resource charge the enclosing transition
has to account for.
-/
structure SelectiveReceive {Carrier SenderId : Type r} {Message : Type w}
    (mailbox : Mailbox Carrier SenderId Message)
    (accepts : MailboxEntry Carrier SenderId Message → Bool) where
  /-- The entries scanned past, in order, none of which matched. -/
  skipped : List (MailboxEntry Carrier SenderId Message)
  /-- The entry taken, if any matched. -/
  selected : Option (MailboxEntry Carrier SenderId Message)
  /-- Everything after it, untouched. -/
  rest : List (MailboxEntry Carrier SenderId Message)
  /--
  The mailbox is exactly the scanned prefix, the selection, and the remainder.

  One equation rather than three side conditions, so nothing can be added or
  lost in the split.
  -/
  exact : mailbox.entries =
    skipped ++ (match selected with | some entry => [entry] | none => []) ++ rest
  /--
  Nothing skipped matched.

  With `exact`, this is what makes the selection the *oldest* match rather than
  an arbitrary one.
  -/
  skippedRejected : ∀ entry ∈ skipped, accepts entry = false
  /-- The selection matched. -/
  selectedAccepted : ∀ entry, selected = some entry → accepts entry = true
  /-- Nothing matched anywhere if nothing was selected. -/
  exhaustedIfNone : selected = none → rest = []
  /-- The resource charge: the length of the prefix actually scanned. -/
  scanWork : Nat
  /-- And it is that length, not a smaller number. -/
  scanWorkExact : scanWork = skipped.length

namespace SelectiveReceive

variable {Carrier SenderId : Type r} {Message : Type w}
  {mailbox : Mailbox Carrier SenderId Message}
  {accepts : MailboxEntry Carrier SenderId Message → Bool}

/--
The selection is the oldest match: no earlier entry in the mailbox accepts.

`docs/PROCESS.md` §3 says selective receive "consumes the oldest matching
occurrence", and this is that, derived from `exact` and `skippedRejected` rather
than asserted separately.
-/
theorem selected_is_oldest (receive : SelectiveReceive mailbox accepts)
    {entry : MailboxEntry Carrier SenderId Message}
    (earlier : entry ∈ receive.skipped) : accepts entry = false :=
  receive.skippedRejected entry earlier

/--
Every skipped occurrence is still in the mailbox afterwards, in its original
relative order.

The heart of "every skipped occurrence retains order, escrow, obligations, and
resource charge". A skipped entry is not consumed and not reordered: the
residual is `skipped ++ rest`, so the scanned prefix is still a prefix.
-/
def residual (receive : SelectiveReceive mailbox accepts) :
    List (MailboxEntry Carrier SenderId Message) :=
  receive.skipped ++ receive.rest

theorem residual_keeps_skipped_prefix (receive : SelectiveReceive mailbox accepts) :
    receive.skipped.IsPrefix receive.residual :=
  ⟨receive.rest, rfl⟩

/--
A receive removes exactly one entry, or none.

The counting law, and the mailbox counterpart of
`Bag.ConsumeExactlyOneMatching.card`: a selective receive cannot quietly drop a
second entry while it is scanning.
-/
theorem residual_length (receive : SelectiveReceive mailbox accepts) :
    mailbox.size =
      receive.residual.length +
        (match receive.selected with | some _ => 1 | none => 0) := by
  unfold Mailbox.size residual
  rw [receive.exact]
  cases receive.selected <;> simp <;> omega

/--
Nothing selected means nothing matched, in the whole mailbox.

`exhaustedIfNone` says the scan reached the end; with `skippedRejected` that
gives the real statement: an empty selection is a proof of absence, not a
scheduling decision to stop looking.
-/
theorem none_means_no_match (receive : SelectiveReceive mailbox accepts)
    (nothing : receive.selected = none)
    {entry : MailboxEntry Carrier SenderId Message}
    (present : entry ∈ mailbox.entries) : accepts entry = false := by
  rw [receive.exact, nothing] at present
  simp [receive.exhaustedIfNone nothing] at present
  exact receive.skippedRejected entry present

/--
Scanning is charged for what it scanned.

An unbounded mailbox scanned to its end costs its length, which is what makes
`docs/PROCESS.md` §3's "neither mechanism is free" enforceable rather than
advisory: the enclosing transition's resource certificate has a number to
account for.
-/
theorem scan_is_charged (receive : SelectiveReceive mailbox accepts) :
    receive.scanWork ≤ mailbox.size := by
  rw [receive.scanWorkExact]
  unfold Mailbox.size
  rw [receive.exact]
  simp

end SelectiveReceive

end Grass.Process
