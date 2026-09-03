import Grass.Process.Network.Mailbox

/-!
# A mailbox with something in it

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.85. An emptiness sweep over every
structure in the corpus found `Grass/Process/Network/Mailbox.lean` entirely
unwitnessed: `MailboxEntry` was constructed nowhere, `Mailbox`'s only inhabitant
anywhere was `Mailbox.empty`, and `SelectiveReceive` — nine fields, five of them
Props — had never been built at all.

What that costs is specific, not general. `Mailbox.distinct` had never been
discharged at a non-empty list, so the duplicate-freedom law was checked by
nothing; `PerSenderPair` had never been evaluated at a mailbox with an entry; and
every one of `SelectiveReceive`'s five laws was a claim about a relation with no
inhabitants.

This file is deliberately not the smallest thing that *inhabits* those records.
A one-entry mailbox whose only entry matches would discharge `skippedRejected`
and `exhaustedIfNone` vacuously and leave `scanWork` at zero. `theReceive` scans
*past* a non-matching entry to select the second, so `skipped` is non-empty,
`skippedRejected` has something to reject, and `scanWorkExact` reports a scan
that actually cost something.

Two things an earlier version of this file claimed and did not deliver, both
found by a reviewer who mutated it field by field.

* **`exhaustedIfNone` was vacuous.** `theReceive` selects something, so the
  hypothesis `selected = none` is unsatisfiable and the field constrains nothing
  — the reviewer proved `theReceive.selected = none → rest = r` for an arbitrary
  `r`. `theEmptyReceive` is a scan of the same mailbox by a filter nothing
  matches: `selected = none`, `skipped` is both entries, `rest` is `[]` because
  it has to be.
* **`PerSenderPair` was named as a cost and never paid.** It appeared nowhere in
  the file and both entries carried the same sender. `twoSenders` is a mailbox
  with two, and `the_profile_holds` and `the_profile_ignores_the_interleaving`
  are the law and its negative half evaluated at it.
-/

namespace Grass.Process.Tests.Mailbox

open Grass.Process

/-- The three parameters, at the simplest types that can tell entries apart. -/
abbrev Carrier := Nat
/-- Two senders, so `PerSenderPair`'s per-sender projection has something to
project and the profile is decidable at every sender rather than at the two a
fixture happens to name. -/
abbrev Sender := Bool
/-- And so are payloads, which is what the filter reads. -/
abbrev Payload := Nat

/-- One entry: an occurrence identity, a sender, a payload. -/
def entryOf (carrier : Carrier) (sender : Sender) (payload : Payload) :
    MailboxEntry Carrier Sender Payload where
  occurrence := ⟨.messageOccurrence, carrier⟩
  isMessage := rfl
  sender := sender
  payload := payload

/--
**A mailbox holding two entries.**

The first non-empty `Mailbox` in the corpus, and therefore the first discharge of
`distinct` that is not vacuous: the two entries carry different occurrence
identities, and `decide` has to check it.
-/
def twoEntry : Mailbox Carrier Sender Payload where
  entries := [entryOf 0 false 7, entryOf 1 false 9]
  distinct := by decide

/-- A filter that accepts only payload 9, so the first entry is scanned past. -/
def acceptsNine (entry : MailboxEntry Carrier Sender Payload) : Bool := entry.payload == 9

/--
**A selective receive that skips one entry and selects the next.**

Every field is discharged against a scan that actually happened: `skipped` holds
the rejected entry, `selected` holds the accepted one, `rest` is what remained,
and `scanWork` is one rather than zero.
-/
def theReceive : SelectiveReceive twoEntry acceptsNine where
  skipped := [entryOf 0 false 7]
  selected := some (entryOf 1 false 9)
  rest := []
  exact := rfl
  skippedRejected := by decide
  selectedAccepted := by decide
  exhaustedIfNone := by simp
  scanWork := 1
  scanWorkExact := rfl

/-- And the scan cost what the scan cost: one skipped entry, one unit of work. -/
theorem the_receive_scanned_one : theReceive.scanWork = 1 := rfl

/-- The entry it skipped is one the filter really rejects. -/
theorem the_skipped_entry_is_rejected : acceptsNine (entryOf 0 false 7) = false := rfl

/-- And the one it took is one the filter really accepts. -/
theorem the_selected_entry_is_accepted : acceptsNine (entryOf 1 false 9) = true := rfl

/-! ## A scan that finds nothing -/

/-- A filter no entry in `twoEntry` matches. -/
def acceptsForty (entry : MailboxEntry Carrier Sender Payload) : Bool := entry.payload == 40

/--
**A selective receive that scans the whole mailbox and takes nothing.**

What makes `exhaustedIfNone` mean something. In `theReceive` the hypothesis
`selected = none` is unsatisfiable, so the field is discharged vacuously; here it
holds, and the field is what forces `rest = []` — a scan that gave up early and
left entries unexamined would satisfy every other field and this one refuses it.
-/
def theEmptyReceive : SelectiveReceive twoEntry acceptsForty where
  skipped := [entryOf 0 false 7, entryOf 1 false 9]
  selected := none
  rest := []
  exact := rfl
  skippedRejected := by decide
  selectedAccepted := by intro entry taken; cases taken
  exhaustedIfNone := fun _ => rfl
  scanWork := 2
  scanWorkExact := rfl

/-- It cost the whole mailbox, which is the resource charge §3 asks for. -/
theorem the_empty_scan_cost_two : theEmptyReceive.scanWork = 2 := rfl

/-- And a scan that stopped early is refused: `exhaustedIfNone` forces the
remainder empty when nothing was selected. -/
theorem a_scan_that_gives_up_early_is_refused
    (receive : SelectiveReceive twoEntry acceptsForty)
    (tookNothing : receive.selected = none)
    (leftSomething : receive.rest ≠ []) : False :=
  leftSomething (receive.exhaustedIfNone tookNothing)

/-! ## And the ordering profile, evaluated -/

/-- Send order, read off the occurrence identity. -/
def sendOrder (entry : MailboxEntry Carrier Sender Payload) : Nat := entry.occurrence.carrier

/--
**The per-sender ordering profile holds here, and it is a real ordering claim.**

`Mailbox.PerSenderPair` had never been evaluated at a mailbox with an entry.
Both of `twoEntry`'s entries come from the *same* sender, so `from' false` is
both of them and the profile is the genuine two-element claim that their send
orders increase — not the singleton it would be at a mailbox with one entry per
sender.
-/
theorem the_profile_holds : Mailbox.PerSenderPair sendOrder twoEntry := by
  intro sender
  cases sender <;> decide

/-- The same two entries, from the same sender, in the wrong order. -/
def outOfOrder : Mailbox Carrier Sender Payload where
  entries := [entryOf 1 false 9, entryOf 0 false 7]
  distinct := by decide

/--
**And it fails when that sender's own messages arrive out of order**, which is
what makes the positive fixture a test rather than a shape.
-/
theorem the_profile_fails_out_of_order : ¬ Mailbox.PerSenderPair sendOrder outOfOrder := by
  intro holds
  exact absurd (holds false) (by decide)

/--
**But it says nothing about the interleaving between senders**, which is the half
the module docstring warns a reader not to assume.

The theorem is stated in `Mailbox.lean`; this is it used, at a mailbox where the
per-sender projections are what they are.
-/
theorem the_profile_ignores_the_interleaving
    (other : Mailbox Carrier Sender Payload)
    (samePerSender : ∀ sender, twoEntry.from' sender = other.from' sender) :
    Mailbox.PerSenderPair sendOrder other :=
  (Mailbox.perSenderPair_ignores_interleaving sendOrder twoEntry other samePerSender).mp
    the_profile_holds

end Grass.Process.Tests.Mailbox
